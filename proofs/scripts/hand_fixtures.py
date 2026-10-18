"""Write the hand-made reward-certificate fixtures of certificate-fixtures/.

The positive fixtures `hand-*.json` follow the format `OpenInfluence.RewardCertificate/v1`
(workspace plan docs/REWARD-CERTIFICATES-PLAN-2026-10-17.md, "The format"). Their K and W
are computed here independently of the Lean checker, by brute-force enumeration over exact
fractions, then rounded to binary64 (Python's float of a Fraction rounds to nearest, ties to
even). Each negative fixture `*.bad.json` is `hand-mixed.json` with one corruption; the
expected failing stage of every fixture is listed in certificate-fixtures/EXPECTED.md.

Run from proofs/: python3 scripts/hand_fixtures.py
"""

from fractions import Fraction as F
from itertools import product
from pathlib import Path
import copy
import json
import struct

OUT = Path("certificate-fixtures")


def word(x):
    return struct.pack(">d", float(x)).hex()


def cell(x, mode):
    if mode == "rational_exact":
        q = F(x)
        return {"q": {"num": str(q.numerator), "den": str(q.denominator)}, "f64": word(q)}
    return {"f64": word(x)}


def attrs(var):
    return {"name": var["name"], "spaceRef": {"tag": "noRef"}, "states": var["states"]}


def variable_data(var, reverse_rows=False):
    rows = [{"name": s, "position": k + 1} for k, s in enumerate(var["states"])]
    if reverse_rows:
        rows = rows[::-1]
    return {"name": var["name"], "spaceRef": {"tag": "noRef"}, "stateRows": rows,
            "rank": var["rank"]}


def certificate(model, mode, description):
    """`model`: variables, mechanisms (chance and decision), utilities, strategy, inputs,
    outputs, flags. Tables hold exact Fractions (or floats, in the inexact fixture)."""
    vs = model["variables"]
    n = [len(v["states"]) for v in vs]
    mechs = model["mechanisms"]
    # Exact reward kernel by enumeration over all generator states.
    gens = [m["target"] for m in mechs]
    ins, outs = model["inputs"], model["outputs"]
    policy = {p["decision"]: p["actions"] for p in model["strategy"]}

    def flat(dims, coords):
        k = 0
        for d, a in zip(dims, coords):
            k = k * d + a
        return k

    K, W = [], []
    for x in product(*[range(n[v]) for v in ins]):
        for y in product(*[range(n[v]) for v in outs]):
            k = w = 0
            for z in product(*[range(n[v]) for v in gens]):
                val = {}
                for v, a in zip(ins, x):
                    val[v] = a
                for v, a in zip(gens, z):
                    val[v] = a
                if any(val[v] != b for v, b in zip(outs, y)):
                    continue
                p = 1
                for m in mechs:
                    pa = [val[v] for v in m["parents"]]
                    if "decision" in m:
                        a = policy[m["decision"]][flat([n[v] for v in m["parents"]], pa)] - 1
                        p *= 1 if val[m["target"]] == a else 0
                    else:
                        dims = [n[v] for v in m["parents"]] + [n[m["target"]]]
                        p *= m["table"][flat(dims, pa + [val[m["target"]]])]
                r = 0
                for u in model["utilities"]:
                    sc = [val[v] for v in u["scope"]]
                    r += u["table"][flat([n[v] for v in u["scope"]], sc)]
                k += p
                w += p * r
            K.append(k)
            W.append(w)
    network = {
        "variableCount": len(vs),
        "variableData": [variable_data(v, v.get("reverse_rows", False)) for v in vs],
        "mechanisms": [
            {"name": m["name"],
             "kernelRef": ({"tag": "policy", "decision": m["decision"]} if "decision" in m
                           else {"tag": "named", "id": m["name"].lower()}),
             "target": m["target"],
             "inputRows": [{"varId": v, "position": k + 1} for k, v in enumerate(m["parents"])]}
            for m in mechs],
        "inputs": [{"varId": v, "attrs": attrs(vs[v])} for v in ins],
        "outputs": [{"varId": v, "attrs": attrs(vs[v])} for v in outs],
    }
    utilities = []
    for u in model["utilities"]:
        rows = [{"varId": v, "position": k + 1} for k, v in enumerate(u["scope"])]
        utilities.append({"name": u["name"], "scopeRows": rows[::-1],
                          "cells": [cell(x, mode) for x in u["table"]]})
    return {
        "format": "OpenInfluence.RewardCertificate/v1",
        "numeric_mode": mode,
        "metadata": {"producer": "hand_fixtures.py", "producer_version": "0.1.0",
                     "julia_version": "none", "description": description},
        "network": network,
        "observability": model["flags"],
        "chance_tables": [{"mechanism": g, "cells": [cell(x, mode) for x in m["table"]]}
                          for g, m in enumerate(mechs) if "decision" not in m],
        "utilities": utilities,
        "strategy": model["strategy"],
        "result": {"arithmetic": "binary64", "K": [{"f64": word(x)} for x in K],
                   "W": [{"f64": word(x)} for x in W]},
    }


FORECAST = {"name": "Forecast", "states": ["sunny", "rainy"], "rank": 0}
SEASON = {"name": "Season", "states": ["wet", "dry"], "rank": 0}
WEATHER = {"name": "Weather", "states": ["rain", "dry"], "rank": 1, "reverse_rows": True}
UMBRELLA = {"name": "Umbrella", "states": ["take", "leave"], "rank": 1}
U = {"name": "U", "scope": [2, 3], "table": [F(70), F(0), F(20), F(100)]}


def mixed(weather_table):
    """Inputs Forecast (observed) and Season (hidden); Weather depends on Season; Umbrella
    reads Forecast; outputs Weather and Umbrella; U reads Weather and Umbrella."""
    return {
        "variables": [FORECAST, SEASON, WEATHER, UMBRELLA],
        "mechanisms": [
            {"name": "Weather", "target": 2, "parents": [1], "table": weather_table},
            {"name": "Umbrella", "decision": "Umbrella", "target": 3, "parents": [0]},
        ],
        "utilities": [U],
        "strategy": [{"decision": "Umbrella", "actions": [2, 1]}],
        "inputs": [0, 1],
        "outputs": [2, 3],
        "flags": {"inputs": ["observed", "hidden"], "outputs": ["hidden", "observed"]},
    }


def closed():
    """The closed umbrella with dyadic tables: K = [1], W = [EU]."""
    weather = {"name": "Weather", "states": ["rain", "dry"], "rank": 0}
    forecast = {"name": "Forecast", "states": ["sunny", "rainy"], "rank": 1}
    umbrella = {"name": "Umbrella", "states": ["take", "leave"], "rank": 2}
    return {
        "variables": [weather, forecast, umbrella],
        "mechanisms": [
            {"name": "Weather", "target": 0, "parents": [], "table": [F(1, 4), F(3, 4)]},
            {"name": "Forecast", "target": 1, "parents": [0],
             "table": [F(1, 4), F(3, 4), F(3, 4), F(1, 4)]},
            {"name": "Umbrella", "decision": "Umbrella", "target": 2, "parents": [1]},
        ],
        "utilities": [{"name": "U", "scope": [0, 2], "table": [F(70), F(0), F(20), F(100)]}],
        "strategy": [{"decision": "Umbrella", "actions": [2, 1]}],
        "inputs": [],
        "outputs": [],
        "flags": {"inputs": [], "outputs": []},
    }


def write(name, cert):
    (OUT / name).write_text(json.dumps(cert, indent=1) + "\n")


def main():
    OUT.mkdir(exist_ok=True)
    base = certificate(mixed([F(3, 4), F(1, 4), F(1, 4), F(3, 4)]), "binary64_exact",
                       "hand-made: dyadic decision half with a hidden input")
    write("hand-mixed.json", base)
    write("hand-closed.json", certificate(closed(), "binary64_exact",
                                          "hand-made: closed dyadic umbrella"))
    write("hand-rational.json",
          certificate(mixed([F(2, 3), F(1, 3), F(1, 3), F(2, 3)]), "rational_exact",
                      "hand-made: rational companions, thirds"))
    write("hand-inexact.json",
          certificate(mixed([0.7, 0.3, 0.3, 0.7]), "binary64_exact",
                      "hand-made: binary64 rows that do not sum to exactly one"))

    def bad(name, corrupt):
        cert = copy.deepcopy(base)
        corrupt(cert)
        cert["metadata"]["description"] = f"negative fixture derived from hand-mixed.json: {name}"
        write(name, cert)

    def hidden(c):
        c["observability"]["inputs"][0] = "hidden"

    def cell_count(c):
        c["chance_tables"][0]["cells"].pop()

    def negative(c):
        c["chance_tables"][0]["cells"][0] = {"f64": word(-0.75)}

    def action(c):
        c["strategy"][0]["actions"][0] = 3

    def k_cell(c):
        c["result"]["K"][1] = {"f64": word(0.5)}

    def w_cell(c):
        c["result"]["W"][1] = {"f64": word(1.0)}

    def flags(c):
        c["observability"]["outputs"].pop()

    bad("hidden-input.bad.json", hidden)
    bad("cell-count.bad.json", cell_count)
    bad("negative-cell.bad.json", negative)
    bad("action-range.bad.json", action)
    bad("k-cell.bad.json", k_cell)
    bad("w-cell.bad.json", w_cell)
    bad("flag-count.bad.json", flags)


if __name__ == "__main__":
    main()
