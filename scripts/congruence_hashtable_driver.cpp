// Differential test driver for the Rust port of libc++'s 'unordered_set'
// (used for 'Closure::GatesTable' in 'src/congruence.rs').
//
// Reads operations from stdin (one per line) and prints a trace.  The Rust
// test 'congruence::tests::libcxx_hash_set_differential' produces the same
// trace with 'LibcxxHashSet' and compares.
//
//   N bc mode   construct a new 'unordered_set (bc, H (mode))'
//   I k         insert k, print "I k <inserted>"
//   E k         erase (find (k)) if found, print "E k <found>"
//   P i         erase the i-th element (iteration order) through its
//               iterator (if any), print "P i <next element or -1>"
//   F k         print "F k <found>"
//   C           clear
//   R n         rehash (n)
//   V n         reserve (n)
//   W m         erase during iteration all k with k % m == 0 (it = erase (it))
//   D           dump: bucket count, size and elements in iteration order
//
// Build: nix develop <flake> -c c++ -std=c++17 -O1 -o driver this.cpp

#include <cstdint>
#include <cstdio>
#include <iostream>
#include <string>
#include <unordered_set>

static uint64_t hash_of (int mode, uint64_t k) {
  switch (mode) {
  case 0:
    return k;
  case 1:
    return k % 13;
  case 2:
    return k * 0x9E3779B97F4A7C15ull ^ (k >> 3);
  default:
    return (k * 2654435761u) & 0xffffff;
  }
}

struct H {
  int mode;
  H (int m = 0) : mode (m) {}
  size_t operator() (uint64_t k) const { return (size_t) hash_of (mode, k); }
};

typedef std::unordered_set<uint64_t, H> Set;

int main () {
  Set *s = nullptr;
  std::string op;
  while (std::cin >> op) {
    if (op == "N") {
      size_t bc;
      int mode;
      std::cin >> bc >> mode;
      delete s;
      s = new Set (bc, H (mode));
      printf ("N %zu\n", s->bucket_count ());
    } else if (op == "I") {
      uint64_t k;
      std::cin >> k;
      bool ins = s->insert (k).second;
      printf ("I %llu %d\n", (unsigned long long) k, (int) ins);
    } else if (op == "E") {
      uint64_t k;
      std::cin >> k;
      auto it = s->find (k);
      bool found = it != s->end ();
      if (found)
        s->erase (it);
      printf ("E %llu %d\n", (unsigned long long) k, (int) found);
    } else if (op == "P") {
      size_t i;
      std::cin >> i;
      long long next = -1;
      if (i < s->size ()) {
        auto it = s->begin ();
        for (size_t j = 0; j < i; ++j)
          ++it;
        auto nx = s->erase (it);
        if (nx != s->end ())
          next = (long long) *nx;
      }
      printf ("P %zu %lld\n", i, next);
    } else if (op == "F") {
      uint64_t k;
      std::cin >> k;
      printf ("F %llu %d\n", (unsigned long long) k,
              (int) (s->find (k) != s->end ()));
    } else if (op == "C") {
      s->clear ();
      printf ("C\n");
    } else if (op == "R") {
      size_t n;
      std::cin >> n;
      s->rehash (n);
      printf ("R %zu %zu\n", n, s->bucket_count ());
    } else if (op == "V") {
      size_t n;
      std::cin >> n;
      s->reserve (n);
      printf ("V %zu %zu\n", n, s->bucket_count ());
    } else if (op == "W") {
      uint64_t m;
      std::cin >> m;
      size_t erased = 0;
      for (auto it = s->begin (); it != s->end ();) {
        if (*it % m == 0)
          it = s->erase (it), ++erased;
        else
          ++it;
      }
      printf ("W %llu %zu\n", (unsigned long long) m, erased);
    } else if (op == "D") {
      printf ("D %zu %zu:", s->bucket_count (), s->size ());
      for (auto k : *s)
        printf (" %llu", (unsigned long long) k);
      printf ("\n");
    }
  }
  delete s;
  return 0;
}
