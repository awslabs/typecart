# OWNER_NAME=aws
# REPO_NAME=aws-cryptographic-material-providers-library-java
OWNER_NAME=cedar-policy
REPO_NAME=cedar-spec
if [ ! -d "$REPO_NAME" ]; then
  git clone git@github.com:$OWNER_NAME/$REPO_NAME.git
fi
cd $REPO_NAME
git fetch origin
# git checkout origin/main
git checkout c519e0f7722673e21f86479cff8f4c2a68c1c8a6
git log --raw > ../commit_logs.txt
cd ..
python3 parse_commit_logs.py -r cedar
