CERTEUS SDK (Go)

- Minimalny klient nad `net/http` dla wybranych endpointów CERTEUS API.
- Brak zewnętrznych zależności; kompatybilny z Go 1.21+.

Pokryte endpointy:
- GET `/v1/pfs/list`
- GET `/v1/pfs/xattrs`
- POST `/v1/proofgate/publish`
- P2P: transport echo, enqueue, job status, queue, dequeue_once

Instalacja:
```bash
go get github.com/CERTEUS/certeus/sdk/go/certeus
```

Użycie:
```go
package main

import (
    "fmt"
    c "github.com/CERTEUS/certeus/sdk/go/certeus"
)

func main() {
    cli := c.New("http://localhost:8081", nil)
    lst, err := cli.PFSList("pfs://public", true, 100, "")
    if err != nil { panic(err) }
    fmt.Println(len(lst.Entries))
}
```

Wydanie modułu:
- Taguj wersje semver `vX.Y.Z` i opublikuj tag
- Dokumentacja: `go doc github.com/CERTEUS/certeus/sdk/go/certeus`
