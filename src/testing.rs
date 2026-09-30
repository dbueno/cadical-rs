//! Port of `testing.hpp`: access to 'internal' for internal testing only.

use crate::external::External;
use crate::internal::Internal;
use crate::solver::Solver;

pub struct Testing<'a> {
    solver: &'a mut Solver,
}

impl<'a> Testing<'a> {
    pub fn new(s: &'a mut Solver) -> Self {
        Testing { solver: s }
    }
    pub fn internal(&mut self) -> &mut Internal {
        self.solver.internal()
    }
    pub fn external(&mut self) -> &mut External {
        self.solver.external()
    }
}
