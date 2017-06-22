#if INTERACTIVE
#r "Newtonsoft.Json"
#endif

open System
open System.Diagnostics
open System.IO
open System.IO.Compression
open Newtonsoft.Json

let DEFAULTARGS = ["AUTO_CONFIG=false"; "-smt2"; "-in"]
let BASHEXEPATH = "c:/Windows/System32/bash.exe"
let SSHENVVARS = "SSH_AUTH_SOCK=/home/baumann/.sshagent.sock" // XXX: workaround WSL limitations :(
let REMOTECMD = "./z3remote.py"
let HOSTENVVAR = "Z3SSHHOSTS"

type Z3Results() = class
    member val result:String = null with get, set
    member val reasonunknown:String = null with get, set
    member val labels:String = null with get, set
    end

let rec ReadLinesUntil endLine = seq {
    match Console.In.ReadLine() with
        | null -> yield null // so caller can detect EOF
        | "(get-info :name)"
            -> Console.Out.WriteLine("(:name \"Z3\")")
               Console.Out.Flush()
               yield! ReadLinesUntil endLine
        | l when l = endLine -> ()
        | l -> yield l + "\n" // include newline delimeter
               yield! ReadLinesUntil endLine
}

let getHosts =
    let hosts = Environment.GetEnvironmentVariable HOSTENVVAR
    if isNull hosts then failwith ("$" + HOSTENVVAR + " must be set to at least one hostname")
    hosts.Split ' ' |> List.ofSeq

let chooseHost (rand:Random, hosts:string list) =
    hosts.[rand.Next(hosts.Length)]

let doQuery chooserState args =
    // construct args, start process
    let argstr = List.fold (fun a b -> a + " " + b) "" args
    let host = chooseHost chooserState
    let remotecmd = SSHENVVARS + " ssh -qx " + host + " " + REMOTECMD + argstr
    let psi = ProcessStartInfo(BASHEXEPATH, sprintf "-c '" + remotecmd + "'")
    psi.UseShellExecute <- false
    psi.RedirectStandardInput <- true
    psi.RedirectStandardOutput <- true
    use p = Process.Start psi

    // capture the query, compress and write to process
    use gzStream = new GZipStream(p.StandardInput.BaseStream, CompressionMode.Compress)
    use bufStream = new BufferedStream(gzStream, 64 * 1024)

    ReadLinesUntil "(check-sat)" |> Seq.iter (fun line ->
        let bytes = System.Text.Encoding.UTF8.GetBytes(line)
        bufStream.Write(bytes, 0, bytes.Length))
    bufStream.Close()
    gzStream.Close()

    // read result json
    let res = JsonConvert.DeserializeObject<Z3Results>(p.StandardOutput.ReadToEnd())
    p.WaitForExit()
    if p.ExitCode <> 0 then failwith "Child SSH process exited uncleanly"

    Console.Out.WriteLine(res.result)
    Console.Out.Flush()

    // interact! return false on EOF, true otherwise
    ReadLinesUntil "(reset)" |> Seq.fold (fun x line ->
        match (if isNull line then null else line.Trim()) with
        | null -> false // get out of here!
        | "(get-info :reason-unknown)"
            -> Console.Out.WriteLine(res.reasonunknown); Console.Out.Flush(); x
        | "(labels)"
            -> Console.Out.WriteLine(res.labels); Console.Out.Flush(); x
        | _ -> x) true

let rec doQueries chooserState args =
    // handle it and repeat until EOF
    if doQuery chooserState args then doQueries chooserState args else ()

[<EntryPoint>]
let main argv =
    match Array.toList argv with
    | ["--version"] -> printfn "Z3 version 4.5.0 - 64 bit"; 0
    | args when Seq.truncate DEFAULTARGS.Length args |> List.ofSeq = DEFAULTARGS
        -> let extraArgs = Seq.skip DEFAULTARGS.Length args |> List.ofSeq
           let chooserState = (System.Random(), getHosts)
           doQueries chooserState extraArgs; 0
    | _ -> printfn "Unsupported arguments"; 1
