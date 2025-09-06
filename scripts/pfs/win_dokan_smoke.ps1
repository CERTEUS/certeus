Write-Host "[+] Windows Dokan smoke"
$d = Get-Command dokanctl -ErrorAction SilentlyContinue
if ($null -eq $d) {
  Write-Error "dokanctl not found"
  exit 2
}
Write-Host "[OK] dokanctl presence verified"
exit 0

