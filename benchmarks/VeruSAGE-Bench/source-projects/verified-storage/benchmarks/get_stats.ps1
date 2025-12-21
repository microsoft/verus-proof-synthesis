# This is a PowerShell script that list of stats of Rust files in the folder

param (
    [string]$dir
)


if ($PSBoundParameters.ContainsKey('dir')) {

	$mydir = ".\$($dir)"

	$files = Get-ChildItem -Path "$($mydir)" -Recurse -File *.rs

	foreach ($file in $files){
		$lineCount = (Get-Content "$($mydir)\$($file)" | Measure-Object -Line).Lines

		if ("$($file)".Contains("L")) {
			$type = "lemma"
		} else {
			$type = "exec"
		}
		Write-Output "$($dir), $type, $($file), $($lineCount)"
	}

} else{
	$mydirs = Get-ChildItem -Path "." -Directory

	foreach ($mydir in $mydirs){
		$files = Get-ChildItem -Path "$($mydir)" -Recurse -File *.rs

		foreach ($file in $files){
			$lineCount = (Get-Content "$($mydir)\$($file)" | Measure-Object -Line).Lines

			if ("$($file)".Contains("L")) {
				$type = "lemma"
			} else {
				$type = "exec"
			}

			Write-Output "$($mydir), $type, $($file), $($lineCount)"
		}
	}
}
