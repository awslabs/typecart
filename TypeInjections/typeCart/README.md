## typeCart features
typeCart offers multiple ways to compare two projects
- projects on local computer:
    * `$ typecart -p [Path to Old Folder] [Path to New Folder] [Path to Output]`
- git commits on a remote repository
    * To keep a clone of commits:
    `$ typecart -c https://gitub.com/[org]/[repo].git [SHA1 of commit] [SHA1 of commit] [Path to Output]`
    * Only print output (remove instance of old and new project):
    `$ typecart -ck https://gitub.com/[org]/[repo].git [SHA1 of commit] [SHA1 of commit] [Path to Output]`
- compare git commits on local repostory:
    * `$ typcart -lc [git commit hash] [git commit hash] [OutputPath]`