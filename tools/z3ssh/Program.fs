open System.Diagnostics

let runSsh argv =
    let args = List.fold (fun a b -> a + " " + b) "" (Array.toList argv)
    let psi = ProcessStartInfo("c:/Windows/System32/bash.exe", "-c 'ssh -Cqx komv01 z3" + args + "'")
    psi.UseShellExecute <- false
    let p = Process.Start psi
    p.WaitForExit()
    p.ExitCode

[<EntryPoint>]
let main argv =
    match argv with
    | [|"--version"|] -> printfn "Z3 version 4.5.0 - 64 bit"; 0
    | _ -> runSsh argv
