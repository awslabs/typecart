namespace typeCart

open LibGit2Sharp
open TypeInjections
open System

module Program =
  
  let getCommit (SHA: string) (location:string) (outputPath:string) : unit =
      let repo = LibGit2Sharp.Repository.Clone(location, outputPath)
      Console.WriteLine("path is " + outputPath)
      use newRepo = new Repository(outputPath)
 
      let commitRepo = newRepo.Lookup<Commit>(SHA)
      Commands.Checkout(newRepo, commitRepo) |>ignore
  
  // based off command line flags, create and provide path for input/output folders
  let interpretFlag  (argvList: string list) : string * string * string =
      let flag = argvList.Item(0)
      
      // -p [inputPath] [inputPath] [outputPath]
      if flag.Contains("-p") then
          
          if argvList.Length < 4 then
            failwith "usage: program -p OLD NEW OUTPUTFOLDER"
            
          Console.WriteLine("***** local project comparison")
          let oldFolderPath = argvList.Item(1)
          let newFolderPath = argvList.Item(2)
          let outFolderPath = argvList.Item(3)
          oldFolderPath, newFolderPath, outFolderPath
          
      // -lc [git commit hash] [git commit hash] [OutputPath]
      elif flag.Contains("-lc") then
          
          if argvList.Length < 4 then
            failwith "usage: program -lc OLD_COMMIT NEW_COMMIT OUTPUTFOLDER"
          
          System.Console.WriteLine("***** git commit")
          // location of repo
          let location = IO.Directory.GetCurrentDirectory()
          
          let commit1 = argvList.Item(1)
          let commit2 = argvList.Item(2)
          let path = argvList.Item(3)
          let pathOld = path + "/Old"
          let pathNew = path + "/New"
              
          // lib2git needs an empty folder to store the repo clones
          for a in [pathOld;pathNew] do
            if System.IO.Directory.Exists(a) then
                System.IO.Directory.Delete(a, true)
          
          getCommit commit1 location pathOld
          getCommit commit2 location pathNew
        
          pathOld, pathNew, path+"/Output"
     
      // -c [github repo url] [github commit hash] [github commit hash] [OutputPath]
      elif flag.Contains("-c") then
          System.Console.WriteLine("***** remote github")
          
          let path = argvList.Item(4)
          let pathOld = path + "/Old"
          let pathNew = path + "/New"
          let url = argvList.Item(1)
          let commit1 = argvList.Item(2)
          let commit2 = argvList.Item(3)
          
          for a in [pathOld;pathNew] do
            if System.IO.Directory.Exists(a) then
                System.IO.Directory.Delete(a, true)
          
          getCommit commit1 url pathOld
          getCommit commit2 url pathNew
          
          
          pathOld, pathNew, path+"/Output"
          
          
      else failwith "flag not found please try again"
      
    
  [<EntryPoint>]
  let main (argv: string array) =
      
      let argvList = argv |> Array.toList
        
      let oldFolderPath, newFolderPath, outputFolderPath = interpretFlag argvList

      TypeInjections.Program.main [|oldFolderPath; newFolderPath; outputFolderPath|]
      
      
      let flag = argvList.Item(0)
      // delete "Old" and "New" folders, 
      if flag.Contains("-ck") then
          System.IO.Directory.Delete(oldFolderPath, true)
          System.IO.Directory.Delete(newFolderPath, true)
      
      0 