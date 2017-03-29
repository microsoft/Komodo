#!/usr/bin/env powershell

$server = "baumann-desk"
$dafny = "tools/Dafny/Dafny.exe"
$remoteboogie = "Boogie.exe"
$args_ignore = @("/ironDafny","/compile:0")
$args_keep = @("/trace")
$argpats_ignore = @("/allocated","/induction")
$argpats_keep = @("/timeLimit","/proverOpt","/proc","/errorTrace")

$dafnyargs = @()
$boogieargs = @()
$dafnysrc = $null
$runlocal = $false

# we must not be compiling
if ($args -notcontains "/compile:0") {
    Write-Warning "Compiling, running locally"
    $runlocal = $true
}

if (-not $runlocal) {
    foreach ($arg in $args) {
        if (($args_ignore -contains $arg) -or
                ($arg.contains(":") -and ($argpats_ignore -contains $arg.split(":")[0]))) {
            $dafnyargs += $arg
        } elseif (($args_keep -contains $arg) -or
                ($arg.contains(":") -and ($argpats_keep -contains $arg.split(":")[0]))) {
            $dafnyargs += $arg
            $boogieargs += $arg
        } elseif ($arg -eq "/noNLarith") {
            $dafnyargs += $arg
            $boogieargs += "/z3opt:smt.arith.nl=false"
        } elseif (-not $arg.StartsWith("/") -and $dafnysrc -eq $null) {
            $dafnysrc = $arg
        } else {
            Write-Warning "Unrecognised arg $arg, running locally"
            $runlocal = $true
            break
        }
    }
}

if ($runlocal -or ($dafnysrc -eq $null)) {
    & $dafny $args
    exit $LastExitCode
}

$localboogiefile = (New-TemporaryFile).FullName
$localargs = "/compile:0","/noVerify","/print:$localboogiefile","/pretty:0"

Write-Host "Invoking Dafny locally..."
& $dafny ($dafnyargs + $localargs + $dafnysrc)
if ($LastExitCode) {
    Remove-Item $localboogiefile -force
    exit $LastExitCode
}

$ErrorActionPreference = "Stop"
$ProgressPreference="SilentlyContinue"

$pss = New-PSSession $server

# create remote temp file
# XXX: Boogie won't look at our file unless it's named *.bpl
# let's blindly hope that we can rename the .tmp file to .bpl without a collision
$remoteboogiefile = Invoke-Command -Session $pss {
    $tmpf = New-TemporaryFile
    $newname = ($tmpf.BaseName + ".bpl")
    Rename-Item $tmpf.FullName $newname
    $tmpf.DirectoryName + "\" + $newname
}

# copy over the boogie output
#Write-Host "Copying local $localboogiefile to remote $remoteboogiefile..."
Copy-Item $localboogiefile -ToSession $pss -Destination $remoteboogiefile

# run boogie; capture its output
Write-Host "Running Boogie remotely..."
# XXX: this is manky, because I need to pass $remoteboogie through the $args
Invoke-Command -Session $pss {& $args[0] $args[1..($args.length-1)]} `
  -ArgumentList (@($remoteboogie) + $boogieargs + $remoteboogiefile) `
  | Tee-Object -Variable boogieoutput

$BoogieExitCode = Invoke-Command -Session $pss {$LastExitCode}

# clean up temp files and session
Invoke-Command -Session $pss {Remove-Item $args -force} -ArgumentList $remoteboogiefile
Remove-PSSession $pss
Remove-Item $localboogiefile -force

if ($BoogieExitCode) {
    exit $BoogieExitCode
} else {
    # boogie appeared to succeed, but it isn't good at reporting
    # failures, so we grep the output to double-check
    if ($boogieoutput | Select-String -CaseSensitive -Quiet -Pattern `
      "^Boogie program verifier finished with [0-9]* verified, 0 errors$") {
        exit 0
    } else {
        exit 1
    }
}
