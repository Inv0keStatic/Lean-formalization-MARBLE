$ErrorActionPreference = 'Stop'
$pegProjectRoot = Split-Path -Parent $PSScriptRoot
$pegElanBin = Join-Path $env:USERPROFILE '.elan\bin'
if (-not (Get-Command lake -ErrorAction SilentlyContinue)) {
    if (Test-Path -LiteralPath (Join-Path $pegElanBin 'lake.exe')) {
        $env:Path = $pegElanBin + ';' + $env:Path
    } else {
        throw 'Lake is unavailable. Install the Lean version specified in lean-toolchain.'
    }
}

Push-Location -LiteralPath $pegProjectRoot
try {
    & lake build
    if ($LASTEXITCODE -ne 0) { throw 'The Lean project did not build.' }

    & lake env lean -DwarningAsError=true AuditCounterexamples.lean
    if ($LASTEXITCODE -ne 0) { throw 'The counterexample dependency check failed.' }

    Write-Output 'Verified'
} finally {
    Pop-Location
}
