// Differential test driver for kitten (C reference side).
//
// Includes 'kitten.c' directly to be able to dump the internal state.
// Reads API calls from a file (one per line) and prints the results.
// The Rust counterpart is 'examples/kitten_driver.rs'; both must print
// identical output.  Build:
//
//   cc -g -O1 -I cadical/src scripts/kitten/kitten_driver.c -o kitten_driver
//   (add -DLOGGING for the logging variant)

#include "../../cadical/src/kitten.c"

static void dump_u (const char *name, const unsigned *b, const unsigned *e) {
  printf ("\n%s", name);
  for (const unsigned *p = b; p != e; p++)
    printf (" %u", *p);
}

static void dump_state (kitten *k) {
  const statistics *st = &k->statistics;
  printf ("state status=%d level=%u propagated=%u unassigned=%u "
          "inconsistent=%u failing=%u generator=%" PRIu64
          " lits=%zu evars=%zu end_original_ref=%zu size=%zu esize=%zu "
          "antecedents=%d learned=%d",
          k->status, k->level, k->propagated, k->unassigned,
          k->inconsistent, k->failing, k->generator, k->lits, k->evars,
          k->end_original_ref, k->size, k->esize, (int) k->antecedents,
          (int) k->learned);
  printf ("\nqueue first=%u last=%u stamp=%" PRIu64 " search=%u",
          k->queue.first, k->queue.last, k->queue.stamp, k->queue.search);
  printf ("\nstats learned=%" PRIu64 " original=%" PRIu64 " flip=%" PRIu64
          " flipped=%" PRIu64 " sat=%" PRIu64 " solved=%" PRIu64
          " conflicts=%" PRIu64 " decisions=%" PRIu64
          " propagations=%" PRIu64 " ticks=%" PRIu64 " unknown=%" PRIu64
          " unsat=%" PRIu64 " limit=%" PRIu64,
          st->learned, st->original, st->kitten_flip, st->kitten_flipped,
          st->kitten_sat, st->kitten_solved, st->kitten_conflicts,
          st->kitten_decisions, st->kitten_propagations, st->kitten_ticks,
          st->kitten_unknown, st->kitten_unsat, k->limits.ticks);
  dump_u ("klauses", k->klauses.begin, k->klauses.end);
  dump_u ("trail", k->trail.begin, k->trail.end);
  dump_u ("units", k->units.begin, k->units.end);
  dump_u ("assumptions", k->assumptions.begin, k->assumptions.end);
  dump_u ("core", k->core.begin, k->core.end);
  dump_u ("export", k->export.begin, k->export.end);
  dump_u ("prime0", k->prime[0].begin, k->prime[0].end);
  dump_u ("prime1", k->prime[1].begin, k->prime[1].end);
  printf ("\nphases");
  for (size_t i = 0; i < k->size / 2; i++)
    printf (" %u", (unsigned) k->phases[i]);
  printf ("\nvalues");
  for (size_t i = 0; i < k->lits; i++)
    printf (" %d", (int) k->values[i]);
  printf ("\nfailed");
  for (size_t i = 0; i < k->lits; i++)
    printf (" %d", (int) k->failed[i]);
  printf ("\nlinks");
  for (size_t i = 0; i < k->lits / 2; i++)
    printf (" %u:%u:%" PRIu64, k->links[i].prev, k->links[i].next,
            k->links[i].stamp);
  printf ("\nvars");
  for (size_t i = 0; i < k->lits / 2; i++)
    if (k->values[2 * i])
      printf (" %u:%u", k->vars[i].level, k->vars[i].reason);
    else
      printf (" -");
  for (size_t lit = 0; lit < k->lits; lit++) {
    printf ("\nwatches[%zu]", lit);
    for (const unsigned *p = k->watches[lit].begin;
         p != k->watches[lit].end; p++)
      printf (" %u", *p);
  }
  printf ("\n");
}

static void print_lits (const char *prefix, size_t size,
                        const unsigned *lits) {
  printf ("%s", prefix);
  for (size_t i = 0; i < size; i++)
    printf (" %u", lits[i]);
  printf ("\n");
}

static void cb_ids (void *state, unsigned id) {
  (void) state;
  printf ("coreid %u\n", id);
}

static void cb_clauses (void *state, bool learned, size_t size,
                        const unsigned *lits) {
  (void) state;
  printf ("coreclause %d", (int) learned);
  print_lits ("", size, lits);
}

static void cb_clauses_id (void *state, unsigned id, bool learned,
                           size_t size, const unsigned *lits) {
  (void) state;
  printf ("coreclauseid %u %d", id, (int) learned);
  print_lits ("", size, lits);
}

static void cb_trace (void *state, unsigned cid, unsigned id, bool learned,
                      size_t size, const unsigned *lits, size_t rsize,
                      const unsigned *rids) {
  (void) state;
  printf ("trace %u %u %d", cid, id, (int) learned);
  print_lits (" lits", size, lits);
  print_lits ("  chain", rsize, rids);
}

static bool cb_ignore (void *state, unsigned id) {
  (void) state;
  return id % 3 == 0;
}

static void cb_implicant (void *state, int side, size_t size,
                          const unsigned *lits) {
  (void) state;
  printf ("implicant %d", side);
  print_lits ("", size, lits);
}

static long term_calls, term_limit;
static int cb_terminator (void *data) {
  (void) data;
  return ++term_calls > term_limit;
}

static unsigned u (int lit) { return int2u (lit); }

#define MAXLITS 4096

int main (int argc, char **argv) {
  if (argc != 2) {
    fprintf (stderr, "usage: kitten_driver <commands>\n");
    return 1;
  }
  FILE *file = fopen (argv[1], "r");
  if (!file) {
    fprintf (stderr, "can not open '%s'\n", argv[1]);
    return 1;
  }
  kitten *k = kitten_init ();
  bool tracked = false;
  char cmd[64];
  int ints[MAXLITS];
  unsigned uns[MAXLITS];
  while (fscanf (file, "%63s", cmd) == 1) {
    printf ("> %s\n", cmd);
    if (!strcmp (cmd, "clear")) {
      kitten_clear (k);
      tracked = false;
    } else if (!strcmp (cmd, "track")) {
      kitten_track_antecedents (k);
      tracked = true;
    } else if (!strcmp (cmd, "log")) {
#ifdef LOGGING
      kitten_set_logging (k);
#endif
    } else if (!strcmp (cmd, "c") || !strcmp (cmd, "x") ||
               !strcmp (cmd, "e") || !strcmp (cmd, "k")) {
      unsigned id = 0;
      int a = 0, b = 0;
      if (cmd[0] != 'k')
        if (fscanf (file, "%u", &id) != 1)
          return 2;
      if (cmd[0] == 'x' || cmd[0] == 'e')
        if (fscanf (file, "%d", &a) != 1)
          return 2;
      if (cmd[0] == 'e')
        if (fscanf (file, "%d", &b) != 1)
          return 2;
      size_t n = 0;
      int lit;
      while (fscanf (file, "%d", &lit) == 1 && lit)
        ints[n] = lit, uns[n] = u (lit), n++;
      if (cmd[0] == 'c')
        citten_clause_with_id (k, id, n, ints);
      else if (cmd[0] == 'x')
        citten_clause_with_id_and_exception (k, id, n, ints, u (a));
      else if (cmd[0] == 'e')
        citten_clause_with_id_and_equivalence (k, id, n, ints, u (a),
                                               u (b));
      else if (n == 1)
        kitten_unit (k, uns[0]);
      else if (n == 2)
        kitten_binary (k, uns[0], uns[1]);
      else
        kitten_clause (k, n, uns);
    } else if (!strcmp (cmd, "a")) {
      int lit;
      if (fscanf (file, "%d", &lit) != 1)
        return 2;
      kitten_assume_signed (k, lit);
    } else if (!strcmp (cmd, "au")) {
      int lit;
      if (fscanf (file, "%d", &lit) != 1)
        return 2;
      kitten_assume (k, u (lit));
    } else if (!strcmp (cmd, "s")) {
      int res = kitten_solve (k);
      printf ("s %d status %d ticks %" PRIu64 "\n", res, kitten_status (k),
              kitten_current_ticks (k));
    } else if (!strcmp (cmd, "limit")) {
      unsigned long long d;
      if (fscanf (file, "%llu", &d) != 1)
        return 2;
      kitten_set_ticks_limit (k, d);
    } else if (!strcmp (cmd, "nolimit")) {
      kitten_no_ticks_limit (k);
    } else if (!strcmp (cmd, "ticks")) {
      printf ("ticks %" PRIu64 "\n", kitten_current_ticks (k));
    } else if (!strcmp (cmd, "term")) {
      long n;
      if (fscanf (file, "%ld", &n) != 1)
        return 2;
      term_calls = 0, term_limit = n;
      kitten_set_terminator (k, 0, cb_terminator);
    } else if (!strcmp (cmd, "noterm")) {
      kitten_no_terminator (k);
    } else if (!strcmp (cmd, "v") || !strcmp (cmd, "vu")) {
      int lit;
      if (fscanf (file, "%d", &lit) != 1)
        return 2;
      if (kitten_status (k) == 10) {
        int v = cmd[1] ? kitten_value (k, u (lit))
                       : kitten_signed_value (k, lit);
        printf ("v %d %d\n", lit, v);
      }
    } else if (!strcmp (cmd, "f")) {
      int lit;
      if (fscanf (file, "%d", &lit) != 1)
        return 2;
      printf ("f %d %d\n", lit, (int) kitten_fixed_signed (k, lit));
    } else if (!strcmp (cmd, "F")) {
      int lit;
      if (fscanf (file, "%d", &lit) != 1)
        return 2;
      if (kitten_status (k) == 20)
        printf ("F %d %d\n", lit, (int) kitten_failed (k, u (lit)));
    } else if (!strcmp (cmd, "p")) {
      int lit;
      if (fscanf (file, "%d", &lit) != 1)
        return 2;
      if (kitten_status (k) == 10)
        printf ("p %d %d\n", lit, (int) kitten_flip_signed_literal (k, lit));
    } else if (!strcmp (cmd, "core")) {
      if (kitten_status (k) == 20 && tracked) {
        uint64_t learned = 0;
        unsigned original = kitten_compute_clausal_core (k, &learned);
        printf ("core %u %" PRIu64 "\n", original, learned);
        kitten_traverse_core_ids (k, 0, cb_ids);
        kitten_traverse_core_clauses (k, 0, cb_clauses);
        kitten_traverse_core_clauses_with_id (k, 0, cb_clauses_id);
        kitten_trace_core (k, 0, cb_trace);
      }
    } else if (!strcmp (cmd, "core0")) {
      if (kitten_status (k) == 20 && tracked) {
        unsigned original = kitten_compute_clausal_core (k, 0);
        printf ("core0 %u\n", original);
      }
    } else if (!strcmp (cmd, "shrink")) {
      if (kitten_status (k) == 21)
        kitten_shrink_to_clausal_core (k);
    } else if (!strcmp (cmd, "rand")) {
      kitten_randomize_phases (k);
    } else if (!strcmp (cmd, "flipph")) {
      kitten_flip_phases (k);
    } else if (!strcmp (cmd, "shuffle")) {
      if (kitten_status (k) == 0)
        kitten_shuffle_clauses (k);
    } else if (!strcmp (cmd, "prime")) {
      if (kitten_status (k) == 10)
        printf ("prime %d\n", kitten_compute_prime_implicant (k, 0, cb_ignore));
    } else if (!strcmp (cmd, "addprime")) {
      int side;
      if (fscanf (file, "%d", &side) != 1)
        return 2;
      if (kitten_status (k) == 11)
        kitten_add_prime_implicant (k, 0, side, cb_implicant);
    } else if (!strcmp (cmd, "jflip")) {
      int lit;
      if (fscanf (file, "%d", &lit) != 1)
        return 2;
      if (kitten_status (k) == 10)
        printf ("jflip %d %d\n", lit,
                kitten_flip_and_implicant_for_signed_literal (k, lit));
    } else if (!strcmp (cmd, "status")) {
      printf ("status %d\n", kitten_status (k));
    } else if (!strcmp (cmd, "dump")) {
      dump_state (k);
    } else {
      fprintf (stderr, "unknown command '%s'\n", cmd);
      return 2;
    }
    fflush (stdout);
  }
  fclose (file);
  kitten_release (k);
  printf ("done\n");
  return 0;
}
