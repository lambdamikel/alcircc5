#!/usr/bin/env python3
"""Validate the machine-readable ConeScheme proof-obligation ledger."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
LEDGER = HERE / "PROOF_OBLIGATIONS.json"


def main() -> int:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}
    assert len(by_id) == len(obligations), "duplicate obligation id"

    required = {"id", "gate", "name", "deps", "exit", "claim"}
    for item in obligations:
        assert required <= set(item), f"missing field in {item.get('id')}"
        assert item["claim"] == "planned", (
            "blueprint must not claim an unbuilt theorem: " + item["id"]
        )
        unknown = set(item["deps"]) - set(by_id)
        assert not unknown, f"{item['id']} has unknown dependencies: {unknown}"

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node: str) -> None:
        if node in visited:
            return
        assert node not in visiting, f"dependency cycle at {node}"
        visiting.add(node)
        for dep in by_id[node]["deps"]:
            visit(dep)
        visiting.remove(node)
        visited.add(node)

    for node in by_id:
        visit(node)

    gates = sorted({item["gate"] for item in obligations})
    assert gates == [f"G{i}" for i in range(7)], f"unexpected gates: {gates}"
    assert by_id["O21"]["name"] == "boolean_decider"
    assert "O20" in by_id["O21"]["deps"]
    assert by_id["O06"]["name"] == "finite_gfp"
    assert by_id["O06"]["gate"] == "G1"

    print(f"PASS: {len(obligations)} obligations, {len(gates)} gates")
    print("PASS: dependency graph is acyclic and closed")
    print("PASS: every theorem remains explicitly marked planned")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
