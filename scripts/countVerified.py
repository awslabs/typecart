import sys
import argparse

def process_dafny_output(lines):
    functions = {}
    current_function = None
    current_category = None

    for line in lines:
        if "Verifying " in line:
            parts = line.split(' ', 2)
            current_function = parts[1]
            current_category = parts[2].strip("() ...")
            if current_function.endswith("_bc"):
                functions.setdefault(current_function, {})[current_category] = 'unverified'
        elif "verified" in line and current_function and current_category:
            if current_function.endswith("_bc"):
                functions[current_function][current_category] = 'verified'
            current_function = None
            current_category = None
        elif "error" in line and current_function and current_category:
            if current_function.endswith("_bc"):
                functions[current_function][current_category] = 'error'
            current_function = None
            current_category = None
        elif "timed out" in line and current_function and current_category:
            if current_function.endswith("_bc"):
                functions[current_function][current_category] = 'timed out'
            current_function = None
            current_category = None

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
        print(f', {len(verified)}, {len(timed_out)}, {len(unverified)}', end='')

if __name__ == "__main__":
    main()
