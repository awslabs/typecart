import subprocess
import time

from collections import defaultdict


run_cedar = True

def count_strings(str, file_name):
    subprocess.run(f'grep -c "{str}" {file_name} > tmp.txt', shell=True)
    with open('tmp.txt', 'r') as f:
        result = int(f.readline().split()[0])
    subprocess.run('rm tmp.txt', shell=True)
    return result


def diff_files(file1, file2):
    subprocess.run(f'diff -y --ignore-blank-lines --suppress-common-lines "{file1}" "{file2}" | wc -l > tmp.txt', shell=True)
    with open('tmp.txt', 'r') as f:
        result = int(f.readline().split()[0])
    subprocess.run('rm tmp.txt', shell=True)
    return result


def run_pr(pr_id, hash_before, hash_after, num_files, run_backward, typecart_args = "", delete_output=False, use_other_combine_dfy=None):
    # if pr_id != 153:
    #     return 0
    # if hash_after != 'd860076a403a03d4b4948279cb6d7c112900608a':
    #     return
    # Reverted commits:
    if hash_after == 'ed7f93d24b6cff8ce6a48bab4dfa8296a833bb17' or hash_after == '5de720f23e6592fa1452ab22bf9626c8fc5c54c2':
        return 0
    if pr_id == -1:
        pr_id = hash_after  # use the hash string
        print(f"Running typeCart for commit {pr_id}...")
    else:
        print(f"Running typeCart for Pull Request #{pr_id}...")
    if run_cedar:
        repo_name = "cedar-spec"
    else:
        repo_name = "aws-cryptographic-material-providers-library-java"
    subprocess.run(f"rm -r old; rm -r new", shell=True)
    subprocess.run(f"cd {repo_name}; git checkout {hash_before if run_backward else hash_after}", shell=True)
    subprocess.run(f"rsync -av --progress {repo_name} old --exclude .git", shell=True)
    subprocess.run(f"cd {repo_name}; git checkout {hash_after if run_backward else hash_before}", shell=True)
    subprocess.run(f"rsync -av --progress {repo_name} new --exclude .git", shell=True)
    subprocess.run(f'printf "{pr_id}, {typecart_args}, {num_files["dfy"]}, " >> result.csv', shell=True)
    if num_files["dfy"] == 0:
        subprocess.run(f'printf "0, 0, 0/0, 0/0, 0, 0\n" >> result.csv', shell=True)
        return 0
    typecart_start = time.time()
    typecart_return_value = subprocess.run(f"../TypeInjections/TypeInjections/bin/Debug/net6.0/TypeInjections old new proofs {typecart_args}", shell=True)
    # subprocess.run(f"../TypeInjections/TypeInjections/bin/Debug/net6.0/TypeInjections old/{repo_name}/StandardLibrary/src new/{repo_name}/StandardLibrary/src combine", shell=True)
    typecart_end = time.time()
    print(f"typeCart returned {typecart_return_value}")
    if use_other_combine_dfy is not None:
        print(f'Use "{use_other_combine_dfy}" as proofs.dfy.')
        pr_id = str(pr_id) + '/' + str(diff_files('proofs/proofs.dfy', use_other_combine_dfy))
        subprocess.run(f'cp "{use_other_combine_dfy}" proofs/proofs.dfy', shell=True)
    num_lemmas = 0
    if typecart_return_value.returncode == 0:
        num_lemmas = count_strings(" lemma ", "proofs/proofs.dfy")  # includes axioms
        num_axioms = count_strings(" {:axiom} ", "proofs/proofs.dfy")
        if num_lemmas == 0 or typecart_args == "-a 1 -p false": # do not run Dafny for this case
            subprocess.run(f'printf "{num_lemmas}, {num_axioms}, 0/0, 0/0, {typecart_end - typecart_start:.02f}, 0\n" >> result.csv', shell=True)
        else:
            subprocess.run(f'printf "{num_lemmas}, {num_axioms}" >> result.csv', shell=True)
            dafny_start = time.time()
            dafny_return_value = subprocess.run(f"dafny verify --warn-shadowing --relax-definite-assignment=false --isolate-assertions --general-traits=datatype --boogie -proverOpt:BATCH_MODE=true --boogie -typeEncoding:a --boogie -timeLimit:20 --boogie -trace --log-format:csv --progress --cores:8 proofs/proofs.dfy > boogie.txt", shell=True)
            dafny_end = time.time()
            print(f"Dafny returned {dafny_return_value}")
            with open('boogie.txt') as f:
                second_to_last_line = ""
                last_line = ""
                for line in f:
                    second_to_last_line = last_line
                    last_line = line
                results_filename = last_line.split(":", 1)[1].strip()
            print(second_to_last_line)
            print(results_filename)
            # e.g., 12 resolution/type errors detected in proofs.dfy
            # e.g., Results File: /Volumes/workplace/typecart/examples/tmp/TestResults/2024-08-13_17_20_27-0.csv
            if second_to_last_line.split(" ", 1)[-1].split(" ")[0] == "resolution/type":
                subprocess.run('echo ", resolution/type error" >> result.csv', shell=True)
            else:
                subprocess.run(f"python3 countVerified.py < {results_filename} >> result.csv", shell=True) # raw numbers
                subprocess.run(f"python3 countVerified.py < {results_filename} > tmp.txt", shell=True)
                with open('tmp.txt', 'r') as f:
                    line = f.readline()
                    verified = int(line.split('/')[0].split(' ')[-1])
                    total = int(line.split('/')[1])
                subprocess.run('rm tmp.txt', shell=True)
                additional_lemmas = num_lemmas - total
                total += additional_lemmas
                verified += additional_lemmas # these are automatically true, no need to verify
                # num_errors = count_strings(": Error: ", "boogie.txt")
                subprocess.run(f'printf ", {verified}/{total}, {typecart_end - typecart_start:.02f}, {dafny_end - dafny_start:.02f}\n" >> result.csv', shell=True)
            if delete_output:
                subprocess.run(f"rm boogie.txt", shell=True)
                subprocess.run(f"rm -r proofs", shell=True)
                subprocess.run(f"rm -r TestResults", shell=True)
    else:
        subprocess.run('echo "typecart error" >> result.csv', shell=True)
    if delete_output:
        subprocess.run(f"rm -r old; rm -r new", shell=True)
    return num_lemmas


def run_pr_with_multiple_config(pr_id, hash_before, hash_after, num_files, run_backward, typecart_args_list):
    for typecart_args in typecart_args_list:
        if run_pr(pr_id, hash_before, hash_after, num_files, run_backward, typecart_args) == 0:
            break  # do not run 0-lemma PRs multiple times


def main(run_backward, typecart_args_list):
    subprocess.run(f'printf "(PR id or commit hash)[/diff lines (ignoring white lines)], typecart args, #Dafny files changed, #lemmas (including axioms), #axioms, #verified/#attempted to verify, #verified/#total lemmas, typeCart running time, Dafny running time\n" >> result.csv', shell=True)
    with open("commit_logs.txt", "r") as f:
        lines = f.readlines()
    commit_hashes = []
    found_pr = set()
    is_between_pr = False
    last_pr_id = -1
    num_files = defaultdict(int)
    for line in lines:
        line = line.strip()
        if len(line) == 0:  # empty line
            continue
        if line.startswith('commit'):
            commit_hashes.append(line[7:])  # "commit abc0123..."
            if is_between_pr:
                assert len(commit_hashes) >= 2
                run_pr_with_multiple_config(last_pr_id, commit_hashes[-1], commit_hashes[-2], num_files, run_backward, typecart_args_list)
                if run_cedar:
                    if last_pr_id == 157 or last_pr_id == 163 or last_pr_id == 197:
                        run_pr(last_pr_id, commit_hashes[-1], commit_hashes[-2], num_files, run_backward, use_other_combine_dfy=f'proofs_{last_pr_id}{"" if run_backward else "_forward"}.dfy')
                if last_pr_id == 1:
                    return  # older histories are not the same repo for cryptools
            elif len(commit_hashes) >= 2:
                # also run it without a PR
                run_pr_with_multiple_config(-1, commit_hashes[-1], commit_hashes[-2], num_files, run_backward, typecart_args_list)
            is_between_pr = False
            num_files = defaultdict(int)
        if line[-1] == ')':
            potential_pr_id = line.split(' ')[-1]
            if potential_pr_id.startswith('(#') and potential_pr_id[2:-1].isnumeric():
                pr_id = int(potential_pr_id[2:-1])  # "... (#pr_id)"
                # assert pr_id not in found_pr
                found_pr.add(pr_id)
                is_between_pr = True
                last_pr_id = pr_id
        if line.endswith('.dfy') or line.endswith('.rs') or line.endswith('.json') or line.endswith('.md'):
            num_files[line.split('.')[-1]] += 1


if __name__ == "__main__":
    main(run_backward=True, typecart_args_list=["-a 1 -p false", "-p false", "", "-h true -p false", "-h true"])
