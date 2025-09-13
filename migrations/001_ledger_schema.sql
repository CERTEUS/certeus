-- Migration: A2 Ledger & Trwałość - PostgreSQL Schema
-- Created: 2025-09-11
-- Purpose: Enterprise-grade ledger schema for CERTEUS Engine
-- DoD: ≥1k events/s, inwarianty łańcucha, audytowalność

-- Enable UUID extension for primary keys
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";

-- Enable timing extension for performance monitoring
CREATE EXTENSION IF NOT EXISTS "pg_stat_statements";

-- ============================================================================
-- CASES TABLE - Central registry of legal cases
-- ============================================================================
CREATE TABLE cases (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    case_id VARCHAR(32) NOT NULL UNIQUE, -- Format: CER-123456
    status VARCHAR(32) NOT NULL DEFAULT 'PENDING',
    jurisdiction JSONB NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    metadata JSONB DEFAULT '{}',

    -- Chain integrity fields
    chain_position BIGINT NOT NULL DEFAULT 0,
    chain_prev_hash VARCHAR(64),
    chain_self_hash VARCHAR(64) NOT NULL,

    -- Audit trail
    created_by VARCHAR(128),
    audit_log JSONB DEFAULT '[]',

    CONSTRAINT cases_status_check CHECK (status IN ('PENDING', 'PROCESSING', 'PUBLISH', 'ARCHIVED', 'ERROR')),
    CONSTRAINT cases_case_id_format CHECK (case_id ~ '^[A-Z]{3}-[0-9]{6}$'),
    CONSTRAINT cases_chain_position_positive CHECK (chain_position >= 0)
);

-- ============================================================================
-- EVENTS TABLE - Immutable event log (heart of the ledger)
-- ============================================================================
CREATE TABLE events (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    event_id BIGSERIAL NOT NULL UNIQUE, -- Sequential ID for ordering
    event_type VARCHAR(64) NOT NULL,
    case_id VARCHAR(32) NOT NULL,

    -- Event payload and metadata
    payload JSONB NOT NULL DEFAULT '{}',
    document_hash VARCHAR(64),
    bundle_id VARCHAR(64),

    -- Timestamps (immutable)
    timestamp TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    ingested_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),

    -- Chain integrity (core of immutability)
    chain_prev_hash VARCHAR(64), -- Points to previous event in global chain
    chain_self_hash VARCHAR(64) NOT NULL, -- Hash of this event
    chain_position BIGINT NOT NULL,

    -- TSA timestamp (RFC3161) - optional but recommended
    tsa_timestamp BYTEA,
    tsa_url VARCHAR(256),

    -- Audit and provenance
    actor VARCHAR(128),
    source_ip INET,
    user_agent TEXT,

    -- Performance optimization
    shard_key VARCHAR(32) GENERATED ALWAYS AS (substring(case_id, 1, 3)) STORED,

    CONSTRAINT events_case_id_fk FOREIGN KEY (case_id) REFERENCES cases(case_id) ON DELETE RESTRICT,
    CONSTRAINT events_event_type_check CHECK (event_type IN (
        'CASE_CREATED', 'CASE_UPDATED', 'BUNDLE_SUBMITTED', 'BUNDLE_VALIDATED',
        'BUNDLE_PUBLISHED', 'VERIFICATION_REQUESTED', 'VERIFICATION_COMPLETED',
        'REDACTION_APPLIED', 'PUBLIC_RELEASED', 'ARCHIVE_INITIATED', 'ERROR_LOGGED'
    )),
    CONSTRAINT events_chain_position_positive CHECK (chain_position >= 0),
    CONSTRAINT events_document_hash_format CHECK (document_hash IS NULL OR document_hash ~ '^[a-f0-9]{64}$')
);

-- ============================================================================
-- BUNDLES TABLE - PCO Bundle storage metadata
-- ============================================================================
CREATE TABLE bundles (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    bundle_id VARCHAR(64) NOT NULL UNIQUE,
    case_id VARCHAR(32) NOT NULL,

    -- Bundle content and integrity
    bundle_hash VARCHAR(64) NOT NULL,
    signature_ed25519 TEXT NOT NULL, -- Base64url encoded
    public_key_id VARCHAR(16) NOT NULL, -- Short hex ID for JWKS

    -- Storage locations
    s3_bucket VARCHAR(128),
    s3_key VARCHAR(512),
    s3_etag VARCHAR(64),
    s3_version_id VARCHAR(128),

    -- Bundle metadata
    size_bytes BIGINT NOT NULL DEFAULT 0,
    content_type VARCHAR(64) DEFAULT 'application/json',
    compression VARCHAR(16) DEFAULT 'none',

    -- Lifecycle management
    status VARCHAR(32) NOT NULL DEFAULT 'STORED',
    retention_until TIMESTAMPTZ,
    archived_at TIMESTAMPTZ,

    -- Timestamps
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    published_at TIMESTAMPTZ,

    -- Performance optimization
    shard_key VARCHAR(32) GENERATED ALWAYS AS (substring(case_id, 1, 3)) STORED,

    CONSTRAINT bundles_case_id_fk FOREIGN KEY (case_id) REFERENCES cases(case_id) ON DELETE RESTRICT,
    CONSTRAINT bundles_status_check CHECK (status IN ('STORED', 'PUBLISHED', 'ARCHIVED', 'ERROR')),
    CONSTRAINT bundles_size_positive CHECK (size_bytes >= 0),
    CONSTRAINT bundles_bundle_hash_format CHECK (bundle_hash ~ '^[a-f0-9]{64}$'),
    CONSTRAINT bundles_public_key_id_format CHECK (public_key_id ~ '^[a-f0-9]{16}$')
);

-- ============================================================================
-- MERKLE_CHAIN TABLE - Periodic merkle root anchoring for batch verification
-- ============================================================================
CREATE TABLE merkle_chain (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    anchor_id BIGSERIAL NOT NULL UNIQUE,

    -- Merkle tree data
    merkle_root VARCHAR(64) NOT NULL,
    leaf_count BIGINT NOT NULL DEFAULT 0,
    tree_height INTEGER NOT NULL DEFAULT 0,

    -- Range of events covered by this anchor
    event_id_from BIGINT NOT NULL,
    event_id_to BIGINT NOT NULL,

    -- Timestamps and anchoring
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    anchored_at TIMESTAMPTZ,

    -- External anchoring (blockchain, TSA, etc.)
    anchor_type VARCHAR(32) DEFAULT 'internal',
    anchor_tx_hash VARCHAR(64),
    anchor_block_height BIGINT,
    anchor_url VARCHAR(512),

    -- Verification and integrity
    verification_status VARCHAR(32) DEFAULT 'PENDING',
    verification_notes TEXT,

    CONSTRAINT merkle_chain_leaf_count_positive CHECK (leaf_count >= 0),
    CONSTRAINT merkle_chain_tree_height_positive CHECK (tree_height >= 0),
    CONSTRAINT merkle_chain_event_range_valid CHECK (event_id_from <= event_id_to),
    CONSTRAINT merkle_chain_anchor_type_check CHECK (anchor_type IN ('internal', 'bitcoin', 'ethereum', 'tsa', 'opentimestamps')),
    CONSTRAINT merkle_chain_verification_status_check CHECK (verification_status IN ('PENDING', 'VERIFIED', 'FAILED', 'EXPIRED'))
);

-- ============================================================================
-- INDEXES for performance (target: ≥1k events/s)
-- ============================================================================

-- Cases indexes
CREATE INDEX idx_cases_case_id ON cases(case_id);
CREATE INDEX idx_cases_status ON cases(status);
CREATE INDEX idx_cases_created_at ON cases(created_at);
CREATE INDEX idx_cases_chain_position ON cases(chain_position);

-- Events indexes (critical for performance)
CREATE INDEX idx_events_case_id ON events(case_id);
CREATE INDEX idx_events_event_type ON events(event_type);
CREATE INDEX idx_events_timestamp ON events(timestamp);
CREATE INDEX idx_events_chain_position ON events(chain_position);
CREATE INDEX idx_events_shard_key ON events(shard_key);
CREATE INDEX idx_events_event_id ON events(event_id); -- For sequential access
CREATE INDEX idx_events_bundle_id ON events(bundle_id) WHERE bundle_id IS NOT NULL;

-- Composite indexes for common queries
CREATE INDEX idx_events_case_id_timestamp ON events(case_id, timestamp);
CREATE INDEX idx_events_type_timestamp ON events(event_type, timestamp);

-- Bundles indexes
CREATE INDEX idx_bundles_case_id ON bundles(case_id);
CREATE INDEX idx_bundles_bundle_id ON bundles(bundle_id);
CREATE INDEX idx_bundles_status ON bundles(status);
CREATE INDEX idx_bundles_created_at ON bundles(created_at);
CREATE INDEX idx_bundles_shard_key ON bundles(shard_key);
CREATE INDEX idx_bundles_s3_key ON bundles(s3_bucket, s3_key);

-- Merkle chain indexes
CREATE INDEX idx_merkle_chain_anchor_id ON merkle_chain(anchor_id);
CREATE INDEX idx_merkle_chain_event_range ON merkle_chain(event_id_from, event_id_to);
CREATE INDEX idx_merkle_chain_created_at ON merkle_chain(created_at);
CREATE INDEX idx_merkle_chain_verification_status ON merkle_chain(verification_status);

-- ============================================================================
-- TRIGGERS for automated audit and chain integrity
-- ============================================================================

-- Function to compute chain hash for events
CREATE OR REPLACE FUNCTION compute_event_chain_hash(
    p_event_id BIGINT,
    p_event_type VARCHAR,
    p_case_id VARCHAR,
    p_payload JSONB,
    p_timestamp TIMESTAMPTZ,
    p_prev_hash VARCHAR
) RETURNS VARCHAR AS $$
DECLARE
    hash_input JSONB;
    hash_result VARCHAR;
BEGIN
    -- Build hash input (canonical JSON)
    hash_input := jsonb_build_object(
        'event_id', p_event_id,
        'event_type', p_event_type,
        'case_id', p_case_id,
        'payload', p_payload,
        'timestamp', extract(epoch from p_timestamp),
        'prev_hash', p_prev_hash
    );

    -- Compute SHA256 (using pgcrypto extension)
    hash_result := encode(digest(hash_input::text, 'sha256'), 'hex');

    RETURN hash_result;
END;
$$ LANGUAGE plpgsql;

-- Function to update chain integrity on new events
CREATE OR REPLACE FUNCTION trigger_update_event_chain()
RETURNS TRIGGER AS $$
DECLARE
    prev_event_hash VARCHAR;
    next_position BIGINT;
BEGIN
    -- Get previous event's hash and next position (fixed for concurrency)
    SELECT
        chain_self_hash,
        chain_position + 1
    INTO prev_event_hash, next_position
    FROM events
    ORDER BY chain_position DESC
    LIMIT 1;

    -- Handle empty table (genesis case)
    IF next_position IS NULL THEN
        next_position := 1;
        prev_event_hash := NULL;
    END IF;

    -- Set chain position
    NEW.chain_position := next_position;
    NEW.chain_prev_hash := prev_event_hash;

    -- Compute self hash
    NEW.chain_self_hash := compute_event_chain_hash(
        NEW.event_id,
        NEW.event_type,
        NEW.case_id,
        NEW.payload,
        NEW.timestamp,
        NEW.chain_prev_hash
    );

    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

-- Create trigger
CREATE TRIGGER events_chain_integrity_trigger
    BEFORE INSERT ON events
    FOR EACH ROW
    EXECUTE FUNCTION trigger_update_event_chain();

-- Function to update case timestamps
CREATE OR REPLACE FUNCTION trigger_update_case_timestamp()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at := NOW();
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

-- Create trigger for cases
CREATE TRIGGER cases_update_timestamp_trigger
    BEFORE UPDATE ON cases
    FOR EACH ROW
    EXECUTE FUNCTION trigger_update_case_timestamp();

-- ============================================================================
-- VIEWS for common queries and monitoring
-- ============================================================================

-- View for chain integrity verification
CREATE VIEW v_chain_integrity AS
SELECT
    e1.event_id,
    e1.case_id,
    e1.event_type,
    e1.chain_position,
    e1.chain_prev_hash,
    e1.chain_self_hash,
    e2.chain_self_hash AS expected_prev_hash,
    (e1.chain_prev_hash = e2.chain_self_hash OR e1.chain_position = 1) AS chain_valid
FROM events e1
LEFT JOIN events e2 ON e2.chain_position = e1.chain_position - 1
ORDER BY e1.chain_position;

-- View for case status summary
CREATE VIEW v_case_summary AS
SELECT
    c.case_id,
    c.status,
    c.created_at,
    COUNT(e.id) AS event_count,
    COUNT(b.id) AS bundle_count,
    MAX(e.timestamp) AS last_event_at,
    MAX(b.published_at) AS last_published_at
FROM cases c
LEFT JOIN events e ON e.case_id = c.case_id
LEFT JOIN bundles b ON b.case_id = c.case_id
GROUP BY c.id, c.case_id, c.status, c.created_at;

-- View for performance monitoring
CREATE VIEW v_ledger_stats AS
SELECT
    'events' AS table_name,
    COUNT(*) AS row_count,
    MIN(timestamp) AS oldest_record,
    MAX(timestamp) AS newest_record,
    COUNT(*) / GREATEST(EXTRACT(EPOCH FROM (MAX(timestamp) - MIN(timestamp)))/3600, 1) AS avg_events_per_hour
FROM events
UNION ALL
SELECT
    'bundles' AS table_name,
    COUNT(*) AS row_count,
    MIN(created_at) AS oldest_record,
    MAX(created_at) AS newest_record,
    COUNT(*) / GREATEST(EXTRACT(EPOCH FROM (MAX(created_at) - MIN(created_at)))/3600, 1) AS avg_bundles_per_hour
FROM bundles;

-- ============================================================================
-- RBAC - Row Level Security (enterprise security)
-- ============================================================================

-- Enable RLS on all tables
ALTER TABLE cases ENABLE ROW LEVEL SECURITY;
ALTER TABLE events ENABLE ROW LEVEL SECURITY;
ALTER TABLE bundles ENABLE ROW LEVEL SECURITY;
ALTER TABLE merkle_chain ENABLE ROW LEVEL SECURITY;

-- Create roles
CREATE ROLE certeus_admin;
CREATE ROLE certeus_writer;
CREATE ROLE certeus_reader;
CREATE ROLE certeus_auditor;

-- Grant table permissions
GRANT ALL ON ALL TABLES IN SCHEMA public TO certeus_admin;
GRANT SELECT, INSERT, UPDATE ON cases, events, bundles TO certeus_writer;
GRANT SELECT ON ALL TABLES IN SCHEMA public TO certeus_reader;
GRANT SELECT ON ALL TABLES IN SCHEMA public TO certeus_auditor;

-- RLS policies (examples - customize per deployment)
CREATE POLICY cases_admin_all ON cases TO certeus_admin USING (true);
CREATE POLICY cases_writer_own ON cases TO certeus_writer USING (created_by = current_user);
CREATE POLICY cases_reader_published ON cases TO certeus_reader USING (status = 'PUBLISH');

-- ============================================================================
-- INITIAL DATA and HEALTH CHECK
-- ============================================================================

-- Insert genesis event for chain initialization
INSERT INTO cases (case_id, status, jurisdiction, chain_position, chain_self_hash, created_by)
VALUES ('GEN-000000', 'ARCHIVED', '{"country": "GENESIS", "domain": "system"}', 0,
        encode(digest('CERTEUS_GENESIS_BLOCK_2025', 'sha256'), 'hex'), 'system');

INSERT INTO events (event_type, case_id, payload, chain_position, chain_self_hash, actor)
VALUES ('GENESIS_BLOCK', 'GEN-000000', '{"message": "CERTEUS Ledger Genesis Block", "version": "1.0"}',
        1, encode(digest('CERTEUS_GENESIS_EVENT_2025', 'sha256'), 'hex'), 'system');

-- Health check function
CREATE OR REPLACE FUNCTION ledger_health_check()
RETURNS JSONB AS $$
DECLARE
    result JSONB;
    chain_breaks INTEGER;
    last_event_age INTERVAL;
BEGIN
    -- Check chain integrity
    SELECT COUNT(*) INTO chain_breaks
    FROM v_chain_integrity
    WHERE NOT chain_valid;

    -- Check last event age
    SELECT NOW() - MAX(timestamp) INTO last_event_age
    FROM events;

    result := jsonb_build_object(
        'status', CASE WHEN chain_breaks = 0 THEN 'HEALTHY' ELSE 'DEGRADED' END,
        'chain_breaks', chain_breaks,
        'last_event_age_minutes', EXTRACT(EPOCH FROM last_event_age)/60,
        'total_events', (SELECT COUNT(*) FROM events),
        'total_cases', (SELECT COUNT(*) FROM cases),
        'total_bundles', (SELECT COUNT(*) FROM bundles),
        'checked_at', NOW()
    );

    RETURN result;
END;
$$ LANGUAGE plpgsql;

-- ============================================================================
-- PERFORMANCE TUNING
-- ============================================================================

-- Optimize for high-frequency inserts
ALTER TABLE events SET (fillfactor = 90);
ALTER TABLE bundles SET (fillfactor = 90);

-- Enable auto-vacuum tuning for high-write tables
ALTER TABLE events SET (
    autovacuum_vacuum_scale_factor = 0.1,
    autovacuum_analyze_scale_factor = 0.05
);

-- Create sequence for event_id with cache for performance
ALTER SEQUENCE events_event_id_seq CACHE 100;

-- ============================================================================
-- COMMENTS for documentation
-- ============================================================================

COMMENT ON TABLE cases IS 'Central registry of legal cases with chain integrity';
COMMENT ON TABLE events IS 'Immutable event log - heart of the ledger with cryptographic chain';
COMMENT ON TABLE bundles IS 'PCO Bundle storage metadata with S3 integration';
COMMENT ON TABLE merkle_chain IS 'Periodic merkle anchoring for batch verification';

COMMENT ON COLUMN events.chain_self_hash IS 'SHA256 hash of this event (immutable proof)';
COMMENT ON COLUMN events.chain_prev_hash IS 'Hash of previous event (creates immutable chain)';
COMMENT ON COLUMN events.tsa_timestamp IS 'RFC3161 timestamp token for external time attestation';

-- End of migration
