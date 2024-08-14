import sys
import argparse

def process_dafny_output(lines):
    functions = {}
    current_function = None
    current_category = None

    for line in lines:
        result = line.split(',')
        parts = result[0].split(' ', 1)
        if not parts[0].endswith("_bc"):
            continue
        current_function = parts[0]
        current_category = parts[1]
        if result[1] == "Passed":
            functions.setdefault(current_function, {})[current_category] = 'verified'
        elif result[1] == "Failed":
            functions.setdefault(current_function, {})[current_category] = 'error'
        else:
            print(f'Unknown result: {result[1]}')

    verified_functions = {k: [c for c, v in categories.items() if v == 'verified'] for k, categories in functions.items() if all(v == 'verified' for v in categories.values())}
    unverified_functions = {k: [c for c, v in categories.items() if v == 'error'] for k, categories in functions.items() if any(v == 'error' for v in categories.values())}
    timed_out_functions = {k: [c for c, v in categories.items() if v == 'timed out'] for k, categories in functions.items() if any(v == 'timed out' for v in categories.values())}

    return verified_functions, unverified_functions, timed_out_functions

def main():
    parser = argparse.ArgumentParser(description="Process Dafny verification output.")
    parser.add_argument("--print-verified", action="store_true", help="Print verified functions.")
    parser.add_argument("--print-unverified", action="store_true", help="Print unverified functions.")
    parser.add_argument("--print", action="store_true", help="Print both verified and unverified functions.")
    parser.add_argument("--categories", action="store_true", help="Include categories in printed names.")

    args = parser.parse_args()

    # Read lines from standard input
    lines = [line.strip() for line in sys.stdin]

    verified, unverified, timed_out = process_dafny_output(lines)

    total_functions = len(verified) + len(unverified)

    if args.print or args.print_verified:
        print("Verified:")
        for function, categories in verified.items():
            if args.categories:
                print(f"{function} in {', '.join(categories)}")
            else:
                print(f"{function}")

    if args.print or args.print_unverified:
        print("\nUnverified:")
        for function, categories in unverified.items():
            if args.categories:
                print(f"{function} in {', '.join(categories)}")
            else:
                print(f"{function}")

    if args.print or args.print_verified or args.print_unverified or args.categories:
        print(f"Number of verified instances: {len(verified)}")
        if args.print or args.print_unverified:
            print(f"Number of unverified instances: {len(unverified)}")
            print(f"Total instances: {total_functions}")
    else:
        print(f', {len(verified)}/{len(verified) + len(unverified)}', end='')
        # print(f', {len(verified)}, {len(timed_out)}, {len(unverified)}', end='')

if __name__ == "__main__":
    main()
