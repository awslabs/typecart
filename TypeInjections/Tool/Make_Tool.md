## How to make dotnet tool
1. open `.fsproj` for the project you want to make a .NET tool for and include the following:
```xml
<PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net6.0</TargetFramework>
    <RootNamespace>typeCart</RootNamespace>

    <PackAsTool>true</PackAsTool>
    <ToolCommandName>typecart</ToolCommandName>
    <PackageOutputPath>./nupkg</PackageOutputPath>

    <PackageId>typecart</PackageId>
    <Version>1.0.0</Version>
    <Authors> [ADD_NAMES] </Authors>
    <Company> [ADD_COMPANY] </Company>

</PropertyGroup>
```
2. Open the terminal in the directory with `.fsproj` file
3. Build the project and create NuGet package
```zsh
$ dotnet pack
```
4. Deploy the tool on the local system using install global tool command
```zsh
$ dotnet tool install --global --add-source ./nupkg typecart
```
5. (optional) Publish tool to internet (NuGet library)
    - Create account on [NuGet.org](https://www.nuget.org/)
    - Click on username in top right corner and go to [API Keys](https://www.nuget.org/account/apikeys)
    - Create API key
        * Give KeyName
        * Set globe pattern to `*`
        * Create API
        * Copy API Key
    - (While still in directory with `.fsproj`) publish nupkg file
    ```zsh
    $ dotnet nuget push nupkg/typecart.[VERSION_HERE].nupkg --api-key [API_KEY_HERE] --source https://api.nuget.org/v3/index.json
    ```
## How users can download tool to use
1. If user has .NET SDK installed: go to [typeCart's Nuget Package](https://www.nuget.org/packages/typecart) page and run terminal command
2. [Coming soon] We will soon publish a typeCart CLI that can run independently of .NET SDK, not sure where we will host this package