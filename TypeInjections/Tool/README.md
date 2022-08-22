## typeCart features
typeCart offers multiple ways to compare two projects
- projects on local computer:
    * `$ typecart -p [OldFolderPath] [NewFolderPath] [OutputPath]`
- git commits on a remote repository:
    * `$ typecart -r https://gitub.com/[org]/[repo].git [old git commit SHA1] [new git commit SHA1] [OutputPath]`
- compare git commits on local repostory:
    * `$ typcart -l [old git commit SHA1] [new git commit SHA1] [OutputPath]`

Future feature: Allow user to specify `Head` as the new git commit