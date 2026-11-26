"""Exhaustive controls for the local SAT encodings."""

import unittest
from itertools import product

from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

from search import Search
from verify import check


def bare(width):
    search = Search.__new__(Search)
    search.width = width
    search.pool = IDPool()
    search.cnf = CNF()
    search.generated = set()
    return search


def assignment(search, row, mask):
    return [search.mem(row, i) if mask & (1 << i) else -search.mem(row, i)
            for i in range(search.width)]


class PrimitiveTests(unittest.TestCase):
    def test_lex_order(self):
        search = bare(4)
        left, right = ("R", 0), ("R", 1)
        search.increasing(left, right)
        with Solver(bootstrap_with=search.cnf.clauses) as solver:
            for a, b in product(range(16), repeat=2):
                self.assertEqual(solver.solve(assumptions=assignment(search, left, a)
                                              + assignment(search, right, b)), a < b)

    def test_intersection_witness(self):
        search = bare(3)
        left, right, x, y = ("R", 0), ("S", 0), ("E", 0), ("E", 1)
        search.closure = [(left, right, [("zero", 0), x, y])]
        search.require_intersection(0)
        with Solver(bootstrap_with=search.cnf.clauses) as solver:
            for values in product(range(8), repeat=4):
                a, b, c, d = values
                assumptions = []
                for row, mask in zip((left, right, x, y), values):
                    assumptions.extend(assignment(search, row, mask))
                self.assertEqual(solver.solve(assumptions=assumptions), a & b in (0, c, d))

    def test_guarded_size_cap_and_full_mask(self):
        search = bare(5)
        guard = search.pool.id()
        row = ("T", 0)
        search.atmost([search.mem(row, i) for i in range(5)], 4, except_full=True, guard=guard)
        with Solver(bootstrap_with=search.cnf.clauses) as solver:
            for mask in range(32):
                assumptions = assignment(search, row, mask)
                self.assertTrue(solver.solve(assumptions=[-guard, *assumptions]))
                self.assertEqual(solver.solve(assumptions=[guard, *assumptions]),
                                 mask == 31 or mask.bit_count() <= 2)

    def test_exact_family_controls(self):
        cube = check(list(range(8)), 3)  # Boolean algebra, exactly half for each point.
        self.assertEqual((cube["frequencies"], cube["missing_unions"]), ([4, 4, 4], 0))
        self.assertFalse(cube["counterexample"])
        singletons = check([1, 2, 4], 3)  # Every pair misses its union.
        self.assertEqual(singletons["missing_unions"], 3)
        self.assertFalse(singletons["counterexample"])


if __name__ == "__main__":
    unittest.main()
