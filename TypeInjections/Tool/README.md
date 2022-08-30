## typeCart features
typeCart CLI offers two ways to compare projects:
- projects on local computer:
  `$ typecart local [--old <path>] [--new <path>] [--print <path>] [--ignore <names>]`
    * Required Options
      * `-o` `--old` Give the absolute path of old project
      * `-n` `--new` Give the absolute path of new project
      * `-p` `--print` Tell typeCart which folder to print out generated files
  * Additional Options
    * `-i` `--ignore` Give list of filenames to ignore when running typeCart
    * (coming soon) `-e` `--entrypoint` Specify certain file(s) to run typeCart on 
- git commits in repository: `$ typecart git [--old <commit>]  [--new <commit>] [--print <path>] [--clone <git URL>] [--ignore <names>]`
  * Required options 
    * `-o` `--old` Give the absolute path of old project
    * `-n` `--new` Give the absolute path of new project
    * `-p` `--print` Tell typeCart which folder to print out generated files
  * Additional Options
    * `-c` `--clone` Provide git URL to checkout commits 
    * `-i` `--ignore` Give list of filenames to ignore when running typeCart 
    * (coming soon) `-e` `--entrypoint` Specify certain file(s) to run typeCart on

External Libraries used in Tool project
* [CommandLineParser.fsharp](https://github.com/commandlineparser/commandline) Popular .NET command line parsing library
* [Lib2GitSharp](https://github.com/libgit2/libgit2sharp/wiki) and [Lib2Git Manual](https://libgit2.org/docs/guides/101-samples/) Easy to use .NET wrapper for git commands 
 

