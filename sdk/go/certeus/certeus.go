// Package certeus provides a minimal client for the CERTEUS API (stub).
package certeus

import (
    "bytes"
    "encoding/json"
    "fmt"
    "io"
    "net/http"
    "net/url"
)

type Client struct {
    BaseURL string
    HTTP    *http.Client
}

func New(baseURL string, httpClient *http.Client) *Client {
    if httpClient == nil {
        httpClient = http.DefaultClient
    }
    return &Client{BaseURL: baseURL, HTTP: httpClient}
}

type PFSListEntry struct {
    URI  string `json:"uri"`
    Size int64  `json:"size"`
}

type PFSListResponse struct {
    Prefix  string         `json:"prefix"`
    Entries []PFSListEntry `json:"entries"`
}

type PFSXattrsResponse struct {
    URI    string                 `json:"uri"`
    Xattrs map[string]interface{} `json:"xattrs"`
}

type PublishRequest struct {
    PCO          map[string]interface{} `json:"pco"`
    BudgetTokens *int                   `json:"budget_tokens,omitempty"`
    Policy       map[string]interface{} `json:"policy,omitempty"`
}

type PublishResponse struct {
    Status    string                 `json:"status"`
    PCO       map[string]interface{} `json:"pco"`
    LedgerRef *string                `json:"ledger_ref"`
}

func (c *Client) doJSON(method, path string, body any, out any) error {
    var rdr io.Reader
    if body != nil {
        b, err := json.Marshal(body)
        if err != nil {
            return err
        }
        rdr = bytes.NewReader(b)
    }
    req, err := http.NewRequest(method, c.BaseURL+path, rdr)
    if err != nil {
        return err
    }
    if body != nil {
        req.Header.Set("content-type", "application/json")
    }
    resp, err := c.HTTP.Do(req)
    if err != nil {
        return err
    }
    defer resp.Body.Close()
    if resp.StatusCode < 200 || resp.StatusCode >= 300 {
        b, _ := io.ReadAll(resp.Body)
        return fmt.Errorf("http %d: %s", resp.StatusCode, string(b))
    }
    if out != nil {
        return json.NewDecoder(resp.Body).Decode(out)
    }
    return nil
}

// PFSList wraps GET /v1/pfs/list.
func (c *Client) PFSList(prefix string, recursive bool, limit int, mime string) (*PFSListResponse, error) {
    q := url.Values{}
    q.Set("prefix", prefix)
    if recursive {
        q.Set("recursive", "true")
    }
    if limit > 0 {
        q.Set("limit", fmt.Sprintf("%d", limit))
    }
    if mime != "" {
        q.Set("mime", mime)
    }
    var out PFSListResponse
    if err := c.doJSON("GET", "/v1/pfs/list?"+q.Encode(), nil, &out); err != nil {
        return nil, err
    }
    return &out, nil
}

// PFSXattrs wraps GET /v1/pfs/xattrs.
func (c *Client) PFSXattrs(uri string) (*PFSXattrsResponse, error) {
    q := url.Values{}
    q.Set("uri", uri)
    var out PFSXattrsResponse
    if err := c.doJSON("GET", "/v1/pfs/xattrs?"+q.Encode(), nil, &out); err != nil {
        return nil, err
    }
    return &out, nil
}

// Publish wraps POST /v1/proofgate/publish.
func (c *Client) Publish(req PublishRequest) (*PublishResponse, error) {
    var out PublishResponse
    if err := c.doJSON("POST", "/v1/proofgate/publish", req, &out); err != nil {
        return nil, err
    }
    return &out, nil
}

