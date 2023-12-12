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


def run_pr(pr_id, hash_before, hash_after, num_files, run_backward, delete_output=False, use_other_combine_dfy=None):
    # if pr_id != 44:
    #     return
    # if hash_after != 'd860076a403a03d4b4948279cb6d7c112900608a':
    #     return
    # Reverted commits:
    if hash_after == 'ed7f93d24b6cff8ce6a48bab4dfa8296a833bb17' or hash_after == '5de720f23e6592fa1452ab22bf9626c8fc5c54c2':
        return
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
    typecart_start = time.time()
    typecart_return_value = subprocess.run(f"../TypeInjections/TypeInjections/bin/Debug/net6.0/TypeInjections old new proofs", shell=True)
    # subprocess.run(f"../TypeInjections/TypeInjections/bin/Debug/net6.0/TypeInjections old/{repo_name}/StandardLibrary/src new/{repo_name}/StandardLibrary/src combine", shell=True)
    typecart_end = time.time()
    print(f"typeCart returned {typecart_return_value}")
    if use_other_combine_dfy is not None:
        print(f'Use "{use_other_combine_dfy}" as proofs.dfy.')
        pr_id = str(pr_id) + '/' + str(diff_files('proofs/proofs.dfy', use_other_combine_dfy))
        subprocess.run(f'cp "{use_other_combine_dfy}" proofs/proofs.dfy', shell=True)
    subprocess.run(f'printf "{pr_id}, {num_files["dfy"]}, " >> result.csv', shell=True)
    if typecart_return_value.returncode == 0:
        num_lemmas = count_strings(" lemma ", "combine/combine.dfy")
        if num_lemmas == 0:
            subprocess.run(f'printf "0, 0, 0, 0, 0, {typecart_end - typecart_start}, 0\n" >> result.csv', shell=True)
        else:
            subprocess.run(f'printf "{num_lemmas}" >> result.csv', shell=True)
            dafny_start = time.time()
            dafny_return_value = subprocess.run(f"dafny verify --boogie -timeLimit:20 --boogie -trace --cores:6 --isolate-assertions combine/combine.dfy > boogie.txt", shell=True)
            dafny_end = time.time()
            print(f"Dafny returned {dafny_return_value}")
            subprocess.run(f"python3 countVerified.py < boogie.txt >> result.csv", shell=True)
            num_errors = count_strings(": Error: ", "boogie.txt")
            subprocess.run(f'printf ", {num_errors}, {typecart_end - typecart_start}, {dafny_end - dafny_start}\n" >> result.csv', shell=True)
            if delete_output:
                subprocess.run(f"rm boogie.txt", shell=True)
                subprocess.run(f"rm -r combine", shell=True)
    else:
        subprocess.run('echo "typecart error" >> result.csv', shell=True)
    if delete_output:
        subprocess.run(f"rm -r old; rm -r new", shell=True)


def main(run_backward=True, no_proof=False):
    subprocess.run(f'printf "(PR id or commit hash)[/diff lines (ignoring white lines)], #Dafny files changed, #lemmas, #verified, #timed out, #errors, #Dafny error count, typeCart running time, Dafny running time\n" >> result.csv', shell=True)
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
                run_pr(last_pr_id, commit_hashes[-1], commit_hashes[-2], num_files, run_backward)
                if run_cedar:
                    if last_pr_id == 111 or last_pr_id == 44:
                        run_pr(last_pr_id, commit_hashes[-1], commit_hashes[-2], num_files, run_backward, use_other_combine_dfy=f'combine_{last_pr_id}_{"" if run_backward else "forward_"}{"no_proof_" if no_proof else ""}{"20231019" if last_pr_id == 44 else "20231025"}.dfy')
                if last_pr_id == 1:
                    return  # older histories are not the same repo for cryptools
            elif len(commit_hashes) >= 2:
                # also run it without a PR
                run_pr(-1, commit_hashes[-1], commit_hashes[-2], num_files, run_backward)
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
    main(run_backward=False, no_proof=False)
