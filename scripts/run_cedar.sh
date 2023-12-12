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
git checkout f8bf292692425b7f062f4863d9d273352b7301dc
git log --raw > ../commit_logs.txt
cd ..
python3 parse_commit_logs.py
