#!/usr/bin/env python3
"""Reject proof placeholders and prohibited declarations in RK, Solution and Test.

Rejected outside comments and strings: sorry, admit, axiom, unsafe, partial, native_decide,
implemented_by, extern, Lean.ofReduceBool, and the kernel-bypass options debug.skipKernelTC and
debug.byAsSorry. Challenge.lean carries the submitted statements with intentional sorry
placeholders, so it is checked only for the two kernel-bypass options. The compiled Test.Axioms
module and an independent kernel replay are separate checks.
"""

from pathlib import Path
import re
import sys

FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|partial|native_decide|implemented_by|extern)\b"
    r"|\bLean\.ofReduceBool\b|\bdebug\.skipKernelTC\b|\bdebug\.byAsSorry\b")
KERNEL_BYPASS = re.compile(r"\bdebug\.skipKernelTC\b|\bdebug\.byAsSorry\b")


def code_without_comments_or_strings(source):
    result = list(source)
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result[index:index + 2] = "  "
                index += 2
            elif pair == "-/":
                depth -= 1
                result[index:index + 2] = "  "
                index += 2
            else:
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif in_string:
            if source[index] == "\\":
                result[index] = " "
                index += 1
                if index < len(source):
                    if source[index] != "\n":
                        result[index] = " "
                    index += 1
            else:
                if source[index] == '"':
                    in_string = False
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif pair == "/-":
            depth = 1
            result[index:index + 2] = "  "
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            result[index:end] = " " * (end - index)
            index = end
        elif source[index] == '"':
            in_string = True
            result[index] = " "
            index += 1
        else:
            index += 1
    if depth or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(result)


def violations(source):
    cleaned = code_without_comments_or_strings(source)
    return [(cleaned.count("\n", 0, match.start()) + 1, match.group())
            for match in FORBIDDEN.finditer(cleaned)]


def main():
    root = Path(__file__).resolve().parent.parent
    files = sorted((root / "RK").rglob("*.lean"))
    solution = root / "Solution.lean"
    if not files or not solution.is_file():
        print("Source guard requires RK/*.lean and Solution.lean", file=sys.stderr)
        return 1
    files.append(solution)
    files.extend(sorted((root / "Test").rglob("*.lean")))
    files.append(root / "Test.lean")
    files.append(root / "RK.lean")
    challenge = root / "Challenge.lean"
    failures = 0
    for path in files:
        try:
            found = violations(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError) as error:
            print(f"{path.relative_to(root)}: {error}", file=sys.stderr)
            failures += 1
            continue
        for line, token in found:
            print(f"{path.relative_to(root)}:{line}: prohibited proof token {token}", file=sys.stderr)
            failures += 1
    try:
        cleaned = code_without_comments_or_strings(challenge.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ValueError) as error:
        print(f"Challenge.lean: {error}", file=sys.stderr)
        failures += 1
    else:
        for match in KERNEL_BYPASS.finditer(cleaned):
            line = cleaned.count("\n", 0, match.start()) + 1
            print(f"Challenge.lean:{line}: prohibited option {match.group()}", file=sys.stderr)
            failures += 1
    if failures:
        return 1
    print(f"Source guard passed for {len(files)} proof files; Challenge checked for kernel-bypass options only.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
