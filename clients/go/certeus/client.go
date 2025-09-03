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
    "encoding/json"
    "fmt"
    "io"
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

