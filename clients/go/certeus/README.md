# CERTEUS Go SDK (minimal)

Użycie:

```go
package main

import (
  "bytes"
  "fmt"
  c "github.com/CERTEUS/certeus/clients/go/certeus"
)

func main() {
  cli := c.New("http://127.0.0.1:8000", "demo")
  h, _ := cli.Health()
  fmt.Println(h)
  pco, _ := cli.GetPublicPCOTyped("case-001")
  fmt.Printf("rid=%s sig=%s\n", pco.Rid, pco.Signature)
  ack, _ := cli.PublishPCOBundleAck("case-001", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "(lfsc)")
  fmt.Println(ack.Ok, ack.DigestHex)
  // analyze upload
  payload := bytes.NewBuffer([]byte("%PDF-1.4. demo"))
  res, _ := cli.Analyze("case-001", "doc.pdf", payload)
  fmt.Println(res["case_id"])
}
```

Uwagi:
- Metody `*Typed` zwracają struktury (`PublicPCO`, `PublishBundleAck`).
- Do uploadu multipart użyj `Analyze()`.
