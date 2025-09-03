# CERTEUS SDK (Go)

Minimalny klient Go dla CERTEUS.

Przykład:

```go
package main

import (
  "fmt"
  c "github.com/CERTEUS/certeus/clients/go/certeus"
)

func main() {
  cli := c.New("http://127.0.0.1:8000", "demo")
  h, _ := cli.Health()
  fmt.Println(h)
}
```

