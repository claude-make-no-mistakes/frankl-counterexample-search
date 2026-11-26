"""Lazy SAT search in the four 55-member complement-fiber cases."""

import argparse
import hashlib
import json
from itertools import combinations, product
from pathlib import Path
from time import perf_counter

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

from verify import check

CASES = {
    "boundary": (14, (14, 14, 14), False),
    "i-a": (13, (15, 14, 14), False),
    "i-b": (13, (15, 15, 13), False),
    "ii": (13, (14, 14, 14), True),
}


def neg(literal):
    if type(literal) is bool:
        return not literal
    return -literal


class Search:
    def __init__(self, case, max_relations=None):
        support, lengths, extra = CASES[case]
        self.support = support
        self.width = support - 2
        self.pool = IDPool()
        self.cnf = CNF()
        w = self.width
        self.arc = {(i, j): self.pool.id(("order", i, j)) for i, j in combinations(range(w), 2)}
        self.groups = {group: [(group, row) for row in range(length)]
                       for group, length in zip("RST", lengths)}
        self.principal = [("D", i) for i in range(w)]
        self.empty = ("zero", 0)
        self.full_fiber = [self.empty] + self.principal
        if extra:
            self.full_fiber.append(("E", 0))
        self.members = [row for rows in self.groups.values() for row in rows] + self.full_fiber
        self.closure = []
        self.generated = set()
        for i, j, k in combinations(range(w), 3):
            self.add(-self.arc[i, j], -self.arc[j, k], self.arc[i, k])
        comparable_cap = len(self.arc) - 20
        if max_relations is not None:
            comparable_cap = min(comparable_cap, max_relations)
        self.atmost(list(self.arc.values()), comparable_cap)
        # Relabel W by decreasing number of strict upper elements. This is
        # a valid linear extension of the domination order.
        for i in range(w - 1):
            earlier = [self.arc[i, j] for j in range(i + 1, w)]
            later = [self.arc[i + 1, j] for j in range(i + 2, w)]
            self.atmost([*later, *(-v for v in earlier)], len(earlier))

        for group, rows in self.groups.items():
            for row in rows:
                self.downset(row)
                self.atmost([self.mem(row, i) for i in range(w)], w - 2 if group != "T" else w - 1,
                            except_full=(group == "T"))
            for left, right in zip(rows, rows[1:]):
                self.increasing(left, right)
            for row in rows[1:]:
                for y in range(w):
                    self.add(neg(self.mem(rows[0], y)), self.mem(row, y))
        # Replace an inclusion-minimal member of P00 by the empty member
        # if necessary. This preserves all four case parameters.
        for y in range(w):
            self.add(self.mem(self.groups["T"][-1], y))
        for row in self.principal:
            self.add(*(neg(self.mem(row, y)) for y in range(w)))
        if extra:
            row = ("E", 0)
            self.downset(row)
            self.add(*(self.mem(row, i) for i in range(w)))
            self.add(*(neg(self.mem(row, i)) for i in range(w)))
            for principal in self.principal:
                self.distinct(row, principal)

        for f in "RS":
            for y in range(w):
                prefix = [neg(self.mem(row, y)) for row in self.groups[f]]
                for row in self.groups["T"]:
                    self.add(*prefix, self.mem(row, y))
        for y in range(w):
            absent = [self.mem(row, y) for row in self.members]
            present = [neg(lit) for lit in absent if type(lit) is not bool]
            present_count = sum(lit is False for lit in absent)
            self.atmost(present, 27 - present_count)
            # In a separating family, a strict domination makes the
            # dominated point strictly less frequent.
            gates = [self.arc[y, j] for j in range(y + 1, w)]
            for f in "RS":
                everyone = self.pool.id()
                witnesses = [self.mem(row, y) for row in self.groups[f]]
                self.add(everyone, *(-v for v in witnesses))
                for v in witnesses:
                    self.add(-everyone, v)
                if f == "R" and case == "i-a":
                    self.atmost(present, 25 - present_count, guard=everyone)
                gates.append(everyone)
            tight = self.pool.id()
            for gate in gates:
                self.add(-gate, tight)
            self.atmost(present, 26 - present_count, guard=tight)

        maximal = []
        for y in range(w):
            flag = self.pool.id()
            strict_upper = [self.arc[y, j] for j in range(y + 1, w)]
            self.add(flag, *strict_upper)
            for arc in strict_upper:
                self.add(-flag, -arc)
            maximal.append(flag)
            # A maximal point has only predecessors and incomparable points.
            self.atmost([self.arc[j, y] for j in range(y)], w - 6, guard=flag)
        self.atmost([-flag for flag in maximal], w - 3)
        for x, y in combinations(range(w), 2):
            joint_max = self.pool.id()
            self.add(-maximal[x], -maximal[y], joint_max)
            common = []
            for z in range(w):
                if z in (x, y):
                    continue
                flag = self.pool.id()
                common.append(flag)
                self.add(-flag, neg(self.arc.get((z, x), False)))
                self.add(-flag, neg(self.arc.get((z, y), False)))
            self.atmost([-flag for flag in common], len(common) - 4, guard=joint_max)
            # A principal ideal cannot contain two distinct maximal points.
            seen_together = []
            for f in "RS":
                flag = self.pool.id()
                seen_together.append(flag)
                for row in self.groups[f]:
                    self.add(-self.mem(row, x), -self.mem(row, y), flag)
            restriction = [-maximal[x], -maximal[y], *(-v for v in seen_together)]
            if extra:
                # The optional P11 complement is the only exception.
                for v in (x, y):
                    self.add(*restriction, self.mem(("E", 0), v))
            else:
                self.add(*restriction)

        for group, rows in self.groups.items():
            for left, right in combinations(rows, 2):
                self.closure.append((left, right, rows))
            for left, right in product(rows, self.full_fiber[1:]):
                self.closure.append((left, right, self.full_fiber))
            if group != "T":
                for left, right in product(rows, self.groups["T"]):
                    self.closure.append((left, right, rows))
        for left, right in product(self.groups["R"], self.groups["S"]):
            self.closure.append((left, right, self.full_fiber))
        for left, right in combinations(self.full_fiber[1:], 2):
            self.closure.append((left, right, self.full_fiber))

    def add(self, *literals):
        if any(lit is True for lit in literals):
            return
        self.cnf.append([lit for lit in literals if lit is not False])

    def mem(self, row, i):
        group, index = row
        if group == "zero":
            return False
        if group == "D":
            return self.arc[i, index] if i < index else i == index
        return self.pool.id(("member", group, index, i))

    def atmost(self, literals, cap, *, except_full=False, guard=True):
        if except_full:
            # An all-one complement in T describes the allowed empty member.
            flag = self.pool.id()
            for lit in literals:
                self.add(-flag, lit)
            cap -= 2  # all nonempty T members contain at least three points
        else:
            flag = False
        if cap < 0:
            self.add(neg(guard), flag)
        elif cap < len(literals):
            clauses = CardEnc.atmost(literals, cap, vpool=self.pool, encoding=EncType.seqcounter)
            for clause in clauses.clauses:
                self.add(neg(guard), flag, *clause)

    def downset(self, row):
        for (i, j), arc in self.arc.items():
            self.add(-arc, neg(self.mem(row, j)), self.mem(row, i))

    def distinct(self, left, right):
        choices = []
        for i in range(self.width):
            a, b = self.mem(left, i), self.mem(right, i)
            differs = self.pool.id()
            choices.append(differs)
            self.add(-differs, a, b)
            self.add(-differs, neg(a), neg(b))
        self.add(*choices)

    def increasing(self, left, right):
        equal_above = True
        witnesses = []
        for i in reversed(range(self.width)):
            a, b = self.mem(left, i), self.mem(right, i)
            less, equal = self.pool.id(), self.pool.id()
            witnesses.append(less)
            self.add(-less, equal_above)
            self.add(-less, -a)
            self.add(-less, b)
            self.add(-equal, equal_above)
            self.add(-equal, -a, b)
            self.add(-equal, a, -b)
            equal_above = equal
        self.add(*witnesses)

    def decode(self, model):
        positive = {v for v in model if v > 0}

        def truth(lit):
            return lit if type(lit) is bool else lit in positive

        return {row: sum(1 << y for y in range(self.width) if truth(self.mem(row, y)))
                for row in self.members}

    def require_intersection(self, key):
        left, right, target = self.closure[key]
        choices = [self.pool.id() for _ in target]
        self.add(*choices)
        for flag, row in zip(choices, target):
            for y in range(self.width):
                a, b, c = (self.mem(r, y) for r in (left, right, row))
                self.add(-flag, neg(c), a)
                self.add(-flag, neg(c), b)
                self.add(-flag, neg(a), neg(b), c)
        self.generated.add(key)

    def refine(self, masks):
        missing = 0
        for key, (left, right, target) in enumerate(self.closure):
            meet = masks[left] & masks[right]
            if all(masks[row] != meet for row in target):
                if key in self.generated:
                    raise RuntimeError("solver model violates a previously encoded intersection")
                self.require_intersection(key)
                missing += 1
        return missing

    def witness(self, masks):
        w = self.width
        flags = {"R": 1, "S": 2, "T": 0, "D": 3, "zero": 3, "E": 3}
        family = sorted((flags[row[0]] << w) | (((1 << w) - 1) ^ mask)
                        for row, mask in masks.items())
        verified = check(family, self.support)
        if not verified["counterexample"] or len(family) != 55:
            raise RuntimeError(f"SAT model failed independent check: {verified}")
        return {"support": self.support, "family": family, "verified": verified}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", choices=CASES)
    parser.add_argument("--max-relations", type=int)
    parser.add_argument("--conflicts", type=int, default=1000000)
    parser.add_argument("--rounds", type=int, default=500)
    parser.add_argument("--all-closure", action="store_true")
    parser.add_argument("--proof", type=Path, help="write DIMACS and DRAT if UNSAT")
    parser.add_argument("--witness", type=Path)
    args = parser.parse_args()
    if args.conflicts < 1 or args.rounds < 1 or (args.max_relations is not None
                                              and args.max_relations < 0):
        parser.error("budgets must be positive and the relation cap nonnegative")
    search = Search(args.case, args.max_relations)
    if args.all_closure:
        for i in range(len(search.closure)):
            search.require_intersection(i)
    start = perf_counter()
    print(json.dumps({"case": args.case, "clauses": len(search.cnf.clauses),
                      "variables": search.cnf.nv, "conflict_budget": args.conflicts,
                      "max_relations": args.max_relations, "all_closure": args.all_closure}), flush=True)
    report = {"status": "unknown", "reason": "round budget"}
    with Solver(name="cadical195", bootstrap_with=search.cnf.clauses,
                with_proof=args.proof is not None) as solver:
        for step in range(args.rounds):
            used = solver.accum_stats()["conflicts"]
            if used >= args.conflicts:
                report = {"status": "unknown", "reason": "conflict budget"}
                break
            solver.conf_budget(args.conflicts - used)
            status = solver.solve_limited()
            if status is None:
                report = {"status": "unknown", "reason": "conflict budget"}
                break
            if not status:
                report = {"status": "unsat"}
                if args.proof:
                    cnf = args.proof.with_suffix(".cnf")
                    proof = args.proof.with_suffix(".drat")
                    search.cnf.to_file(str(cnf))
                    lines = solver.get_proof()
                    if not lines:
                        raise RuntimeError("no DRAT proof was exported")
                    proof.write_bytes(("\n".join(lines) + "\n").encode("ascii"))
                    report["cnf_sha256"] = hashlib.sha256(cnf.read_bytes()).hexdigest()
                break
            masks = search.decode(solver.get_model())
            previous = len(search.cnf.clauses)
            if not search.refine(masks):
                witness = search.witness(masks)
                if args.witness:
                    args.witness.write_text(json.dumps(witness, indent=2) + "\n", encoding="ascii")
                report = {"status": "sat", **witness}
                break
            solver.append_formula(search.cnf.clauses[previous:])
        print(json.dumps({**report, "case": args.case, "max_relations": args.max_relations,
                          "rounds": step + 1, "closure_constraints": len(search.generated),
                          "clauses": len(search.cnf.clauses), "omitted_closure": (
                              len(search.closure) - len(search.generated)),
                          "seconds": round(perf_counter() - start, 3),
                          **solver.accum_stats()}), flush=True)


if __name__ == "__main__":
    main()
