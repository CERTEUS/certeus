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

// P2P types
type P2PEnqueueRequest struct {
    Device  string                 `json:"device"`
    Payload map[string]interface{} `json:"payload,omitempty"`
}

type P2PEnqueueResponse struct {
    JobID   string `json:"job_id"`
    Status  string `json:"status"`
    ETAHint string `json:"eta_hint"`
}

type P2PJobStatusResponse struct {
    JobID   string                 `json:"job_id"`
    Status  string                 `json:"status"`
    Device  string                 `json:"device"`
    Payload map[string]interface{} `json:"payload"`
}

type P2PQueueSummaryResponse struct {
    Depth    int               `json:"depth"`
    ByDevice map[string]int    `json:"by_device"`
}

type P2PTransportEchoResponse struct {
    A       string `json:"a"`
    B       string `json:"b"`
    OK      bool   `json:"ok"`
    Len     int    `json:"len"`
    Message string `json:"message"`
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

// P2P transport echo
func (c *Client) P2PTransportEcho(msg string) (*P2PTransportEchoResponse, error) {
    if msg == "" {
        msg = "synapse"
    }
    var out P2PTransportEchoResponse
    path := "/v1/p2p/transport/echo?msg=" + url.QueryEscape(msg)
    if err := c.doJSON("GET", path, nil, &out); err != nil {
        return nil, err
    }
    return &out, nil
}

// P2P queue
func (c *Client) P2PEnqueue(req P2PEnqueueRequest) (*P2PEnqueueResponse, error) {
    var out P2PEnqueueResponse
    if err := c.doJSON("POST", "/v1/p2p/enqueue", req, &out); err != nil {
        return nil, err
    }
    return &out, nil
}

func (c *Client) P2PJobStatus(jobID string) (*P2PJobStatusResponse, error) {
    var out P2PJobStatusResponse
    if err := c.doJSON("GET", "/v1/p2p/jobs/"+url.PathEscape(jobID), nil, &out); err != nil {
        return nil, err
    }
    return &out, nil
}

func (c *Client) P2PQueueSummary() (*P2PQueueSummaryResponse, error) {
    var out P2PQueueSummaryResponse
    if err := c.doJSON("GET", "/v1/p2p/queue", nil, &out); err != nil {
        return nil, err
    }
    return &out, nil
}

func (c *Client) P2PDequeueOnce() (*P2PJobStatusResponse, error) {
    var out P2PJobStatusResponse
    if err := c.doJSON("POST", "/v1/p2p/dequeue_once", nil, &out); err != nil {
        return nil, err
    }
    return &out, nil
}
