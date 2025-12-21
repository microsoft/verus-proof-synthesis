# This is a PowerShell script that verify all Rust files in the current folder

param (
    [string]$name,
    [string]$dir
)


if ($PSBoundParameters.ContainsKey('dir')) {

	$mydir = ".\$($dir)"

	if ($PSBoundParameters.ContainsKey('name')) {
		$files = Get-ChildItem -Path "$($mydir)" -File "*$($name)*.rs"
	}else{
		$files = Get-ChildItem -Path "$($mydir)" -File *.rs
	}

	foreach ($file in $files) {
		Write-Output "Verifying file $($file) ..."
		verus.exe "$($mydir)\$($file)" --expand-errors -L dependency=../deps_hack/target/debug/deps --extern=deps_hack=../deps_hack/target/debug/libdeps_hack.rlib
	}

} else{

	$mydirs = Get-ChildItem -Path "." -Directory


	foreach ($mydir in $mydirs){
		if ($PSBoundParameters.ContainsKey('name')) {
			$files = Get-ChildItem -Path "$($mydir)" -File "*$($name)*.rs"
		}else{
			$files = Get-ChildItem -Path "$($mydir)" -File *.rs
		}

		foreach ($file in $files) {
			Write-Output "Verifying file $($file) ..."
			verus.exe "$($mydir)\$($file)"  --expand-errors -L dependency=../deps_hack/target/debug/deps --extern=deps_hack=../deps_hack/target/debug/libdeps_hack.rlib
		}
	}
}
