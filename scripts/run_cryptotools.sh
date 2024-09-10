OWNER_NAME=aws
REPO_NAME=aws-cryptographic-material-providers-library-java
if [ ! -d "$REPO_NAME" ]; then
  git clone git@github.com:$OWNER_NAME/$REPO_NAME.git --recursive
fi
cd $REPO_NAME
git fetch origin
# git checkout origin/main
git checkout a0416d96bdba385e1988067715db26ba3d4cd33c
git log --raw > ../commit_logs.txt
cd ..
python3 parse_commit_logs.py -r cryptotools
