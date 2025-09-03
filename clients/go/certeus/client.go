// +-------------------------------------------------------------+
// |                          CERTEUS                            |
// +-------------------------------------------------------------+
// | FILE: clients/go/certeus/client.go                          |
// | ROLE: Go SDK client                                          |
// | PLIK: clients/go/certeus/client.go                          |
// | ROLA: Klient SDK w Go                                        |
// +-------------------------------------------------------------+

package certeus

import (
    "bytes"
    "encoding/json"
    "fmt"
    "io"
    "mime/multipart"
    "net/http"
    "time"
)

// Client is a minimal CERTEUS HTTP client.
type Client struct {
    BaseURL  string
    TenantID string
    httpc    *http.Client
}

// New creates a new client with optional tenant ID.
func New(baseURL string, tenantID string) *Client {
    if baseURL == "" {
        baseURL = "http://127.0.0.1:8000"
    }
    return &Client{
        BaseURL:  baseURL,
        TenantID: tenantID,
        httpc:    &http.Client{Timeout: 15 * time.Second},
    }
}

func (c *Client) url(path string) string { return c.BaseURL + path }

func (c *Client) doJSON(req *http.Request, out any) error {
    if c.TenantID != "" {
        req.Header.Set("X-Tenant-ID", c.TenantID)
    }
    resp, err := c.httpc.Do(req)
    if err != nil {
        return err
    }
    defer resp.Body.Close()
    if resp.StatusCode < 200 || resp.StatusCode >= 300 {
        b, _ := io.ReadAll(resp.Body)
        return fmt.Errorf("http %d: %s", resp.StatusCode, string(b))
    }
    dec := json.NewDecoder(resp.Body)
    return dec.Decode(out)
}

// OpenAPI fetches /openapi.json.
func (c *Client) OpenAPI() (map[string]any, error) {
    req, _ := http.NewRequest(http.MethodGet, c.url("/openapi.json"), nil)
    var data map[string]any
    err := c.doJSON(req, &data)
    return data, err
}

// Health fetches /health.
func (c *Client) Health() (map[string]any, error) {
    req, _ := http.NewRequest(http.MethodGet, c.url("/health"), nil)
    var data map[string]any
    err := c.doJSON(req, &data)
    return data, err
}

// GetPublicPCO fetches /pco/public/{case_id}.
func (c *Client) GetPublicPCO(caseID string) (map[string]any, error) {
    req, _ := http.NewRequest(http.MethodGet, c.url("/pco/public/"+caseID), nil)
    var data map[string]any
    err := c.doJSON(req, &data)
    return data, err
}

// PublishPCOBundle posts a minimal ProofBundle creation request.
func (c *Client) PublishPCOBundle(rid, smt2Hash, lfsc string) (map[string]any, error) {
    body := map[string]any{
        "rid":       rid,
        "smt2_hash": smt2Hash,
        "lfsc":      lfsc,
    }
    b, _ := json.Marshal(body)
    req, _ := http.NewRequest(http.MethodPost, c.url("/v1/pco/bundle"), bytes.NewReader(b))
    req.Header.Set("Content-Type", "application/json")
    var data map[string]any
    err := c.doJSON(req, &data)
    return data, err
}

// Analyze uploads a file (multipart) and returns analysis JSON.
func (c *Client) Analyze(caseID string, filename string, r io.Reader) (map[string]any, error) {
    var buf bytes.Buffer
    mw := multipart.NewWriter(&buf)
    fw, err := mw.CreateFormFile("file", filename)
    if err != nil { return nil, err }
    if _, err := io.Copy(fw, r); err != nil { return nil, err }
    _ = mw.Close()
    req, _ := http.NewRequest(http.MethodPost, c.url("/v1/analyze?case_id="+caseID), &buf)
    req.Header.Set("Content-Type", mw.FormDataContentType())
    var data map[string]any
    if c.TenantID != "" { req.Header.Set("X-Tenant-ID", c.TenantID) }
    err = c.doJSON(req, &data)
    return data, err
}
