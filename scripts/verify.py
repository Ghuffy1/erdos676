"""Build the pinned project and retain exact target and axiom evidence."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
TARGETS = [
    "Erdos676.erdos676_negative",
    "Erdos676.erdos676_infinite_exceptions",
    "Erdos676.full_quantitative_disproof",
    "JSP000549.question_equivalent",
    "JSP000549.original_question_negative",
    "JSP000549.arbitrarily_large_exceptions",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def tracked_hashes():
    files = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).split(b"\0")
    return {
        item.decode("utf-8"): sha256(ROOT / item.decode("utf-8"))
        for item in files if item
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output", type=Path, default=Path("verification/local"))
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--timeout", type=int, default=7200)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    before = tracked_hashes()
    initial_status = git("status", "--porcelain", "--untracked-files=no")
    if initial_status:
        raise RuntimeError("Commit the source and configuration before verifying it.")
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    records = []
    audit_text = ""
    report = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "commit": git("rev-parse", "HEAD"),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "manifest_sha256": sha256(ROOT / "lake-manifest.json"),
        "project_outputs_present_before": (ROOT / ".lake/build").exists(),
        "commands": records,
        "source_hashes": before,
        "replay_requested": args.replay,
        "independent_external_checker": "not performed",
    }
    commands = [
        ("version", [args.lake, "env", "lean", "--version"]),
        ("build", [args.lake, "build"]),
        ("targets", [args.lake, "build", "+Erdos676.ExactStatement", "+Erdos676.FullDisproof", "+SubmissionAudit"]),
        ("axioms", [args.lake, "env", "lean", "audit/SubmissionAudit.lean"]),
    ]
    if args.replay:
        commands.append(("replay", [args.lake, "env", "leanchecker", "--fresh", "Erdos676.ExactStatement"]))
    try:
        for name, command in commands:
            log = output / (name + ".log")
            started = datetime.now(timezone.utc).isoformat()
            print("Running " + name, flush=True)
            with log.open("w", encoding="utf-8") as stream:
                result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                        stderr=subprocess.STDOUT, timeout=args.timeout)
            records.append({"name": name, "command": command, "started_utc": started,
                            "finished_utc": datetime.now(timezone.utc).isoformat(),
                            "exit_code": result.returncode, "log": log.name,
                            "log_sha256": sha256(log)})
            if result.returncode:
                print(log.read_text(encoding="utf-8", errors="replace")[-12000:])
                raise RuntimeError(name + " failed")
            if name == "axioms":
                audit_text = log.read_text(encoding="utf-8", errors="replace")
        rows = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit_text))
        for target in TARGETS:
            if target not in rows:
                raise RuntimeError("Missing axiom output for " + target)
            axioms = {item.strip() for item in rows[target].split(",") if item.strip()}
            if not axioms <= ALLOWED_AXIOMS:
                raise RuntimeError("Unexpected axioms for " + target + ": " + str(axioms))
        if before != tracked_hashes() or initial_status != git("status", "--porcelain", "--untracked-files=no"):
            raise RuntimeError("Tracked source changed during verification")
        report["targets"] = rows
        report["tracked_source_unchanged"] = True
        report["mechanical_result"] = "passed with standard axioms only"
        print(report["mechanical_result"], flush=True)
    except Exception as error:
        report["mechanical_result"] = "incomplete or failed"
        report["error"] = str(error)
        raise
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (output / "run.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
