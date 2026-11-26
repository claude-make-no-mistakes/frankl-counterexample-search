"""Verify an explicit family given by its member masks."""

import argparse
import json
from itertools import combinations
from pathlib import Path


def check(family, support):
    if type(support) is not int or support < 1:
        raise ValueError("support size must be positive")
    if not isinstance(family, list) or not family:
        raise ValueError("family must be a nonempty list")
    if any(type(member) is not int or not 0 <= member < 1 << support for member in family):
        raise ValueError("invalid member mask")
    present = set(family)
    if len(present) != len(family):
        raise ValueError("members must be distinct")
    universe = 0
    for member in family:
        universe |= member
    if universe != (1 << support) - 1:
        raise ValueError("declared support does not match the union")
    missing = [(a, b) for a, b in combinations(family, 2) if a | b not in present]
    frequencies = [sum((member >> x) & 1 for member in family) for x in range(support)]
    return {"members": len(family), "support": support, "frequencies": frequencies,
            "missing_unions": len(missing),
            "counterexample": not missing and 2 * max(frequencies) < len(family)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness", type=Path)
    args = parser.parse_args()
    data = json.loads(args.witness.read_text(encoding="utf-8"))
    print(json.dumps(check(data["family"], data["support"])))


if __name__ == "__main__":
    main()
