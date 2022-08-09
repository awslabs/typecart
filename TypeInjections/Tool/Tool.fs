
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace Tool

open System.IO
open System
open TypeInjections

module Tester = 
                           

    [<EntryPoint>]
    let main (argv: string array) =
        
        Utils.log "***** Entering Tool.fs"
        
        0