Get-Process python -ErrorAction SilentlyContinue |
  Sort-Object WorkingSet64 -Descending |
  Select-Object -First 6 Id,
    @{n='GB';e={[math]::Round($_.WorkingSet64/1GB,1)}},
    @{n='CPUs';e={[math]::Round($_.CPU)}}
