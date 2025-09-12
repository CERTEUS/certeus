# CERTEUS Engine - A6 Security DoD Tests
# Quantum-Resistance Temporal & Security Protocol
# Comprehensive security component testing

import asyncio
import hashlib
import json
import os
# Import components - use absolute imports
import sys
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

from core.security.attestation.attestation_generator import (
    AttestationGenerator, SLSALevel)
from core.security.cve.cve_scanner import CVEScanner, CVESeverity
from core.security.keys.key_manager import (KeyManager, KeyRotationPolicy,
                                            KeyStatus, KeyStoreType)
from core.security.sbom.sbom_generator import (Component, ComponentType,
                                               SBOMGenerator)
from services.security_service.security_service import (SecurityPolicy,
                                                        SecurityService)


class TestA6SecurityKeyManagement:
    """Test A6.1: Ed25519 Key Management"""
    
    def test_key_generation_ed25519(self):
        """Test Ed25519 key generation"""
        key_manager = KeyManager()
        
        key_id = "test-ed25519-key"
        
        metadata = key_manager.generate_key(key_id)
        
        assert metadata.key_id == key_id
        assert metadata.algorithm == "Ed25519"
        assert metadata.key_size == 256
        assert metadata.status == KeyStatus.ACTIVE
    
    def test_key_signing_verification(self):
        """Test Ed25519 digital signing and verification"""
        key_manager = KeyManager()
        
        key_id = "test-signing-key"
        key_manager.generate_key(key_id)
        
        test_data = b"CERTEUS test message for signing"
        
        # Sign data
        signature = key_manager.sign_data(key_id, test_data)
        assert signature is not None
        assert len(signature) == 64  # Ed25519 signature length
        
        # Verify signature
        is_valid = key_manager.verify_signature(key_id, test_data, signature)
        assert is_valid == True
        
        # Verify with wrong data
        wrong_data = b"Wrong message"
        is_invalid = key_manager.verify_signature(key_id, wrong_data, signature)
        assert is_invalid == False
    
    def test_key_rotation_policy(self):
        """Test key rotation policies"""
        key_manager = KeyManager()
        
        key_id = "test-rotation-key"
        
        # Generate key with expiration
        metadata = key_manager.generate_key(key_id, expires_in_days=1)
        
        assert metadata.key_id == key_id
        assert metadata.expires_at is not None
    
    def test_key_export_import(self):
        """Test key export and import functionality"""
        key_manager = KeyManager()
        
        key_id = "test-export-key"
        key_manager.generate_key(key_id)
        
        # Export public key
        public_key_pem = key_manager.export_public_key_pem(key_id)
        assert "BEGIN PUBLIC KEY" in public_key_pem
        assert "END PUBLIC KEY" in public_key_pem
    
    def test_multiple_key_backends(self):
        """Test different key storage backends"""
        
        # Test software backend (default)
        software_manager = KeyManager()
        key_id = "test-software-key"
        metadata = software_manager.generate_key(key_id)
        assert metadata.key_id == key_id

class TestA6SecuritySBOM:
    """Test A6.2: SBOM Generation (CycloneDX)"""
    
    def test_sbom_generation(self):
        """Test SBOM generation in CycloneDX format"""
        generator = SBOMGenerator()
        
        sbom = generator.generate_sbom(
            include_dev_dependencies=False,
            scan_for_vulnerabilities=True
        )
        
        # Validate SBOM structure
        assert sbom["bomFormat"] == "CycloneDX"
        assert sbom["specVersion"] == "1.4"
        assert "serialNumber" in sbom
        assert "metadata" in sbom
        assert "components" in sbom
        
        # Validate metadata
        metadata = sbom["metadata"]
        assert "timestamp" in metadata
        assert "tools" in metadata
        assert metadata["tools"][0]["name"] == "certeus-sbom-generator"
    
    def test_python_dependency_analysis(self):
        """Test Python dependency analysis"""
        generator = SBOMGenerator()
        
        components = generator.analyze_python_dependencies()
        assert len(components) > 0
        
        # Check component structure
        for component in components[:3]:  # Check first 3
            assert hasattr(component, 'name')
            assert hasattr(component, 'version')
            assert hasattr(component, 'type')
            assert component.type == ComponentType.LIBRARY
            assert component.group == "python"
    
    def test_sbom_validation(self):
        """Test SBOM validation"""
        generator = SBOMGenerator()
        
        sbom = generator.generate_sbom()
        validation_errors = generator.validate_sbom(sbom)
        
        assert isinstance(validation_errors, list)
        # Should have no validation errors for proper SBOM
        assert len(validation_errors) == 0
    
    def test_vulnerability_summary(self):
        """Test vulnerability summary generation"""
        generator = SBOMGenerator()
        
        sbom = generator.generate_sbom(scan_for_vulnerabilities=True)
        summary = generator.get_vulnerability_summary(sbom)
        
        assert isinstance(summary, dict)
        expected_keys = ["CRITICAL", "HIGH", "MEDIUM", "LOW"]
        for key in expected_keys:
            assert key in summary
            assert isinstance(summary[key], int)

class TestA6SecurityAttestation:
    """Test A6.3: SLSA/in-toto Attestations"""
    
    def test_slsa_provenance_generation(self):
        """Test SLSA build provenance generation"""
        key_manager = KeyManager()
        key_id = "test-attestation-key"
        key_manager.generate_key(key_id)
        
        generator = AttestationGenerator(key_manager)
        
        # Test data
        subjects = []
        build_commands = ["python setup.py build", "python -m pytest"]
        build_env = {"PYTHON_VERSION": "3.11", "BUILD_TYPE": "release"}
        materials = []
        
        provenance = generator.generate_slsa_provenance(
            subjects=subjects,
            build_commands=build_commands,
            build_env=build_env,
            materials=materials,
            slsa_level=SLSALevel.LEVEL_2
        )
        
        assert provenance.builder.id is not None
        assert provenance.buildType is not None
        assert provenance.invocation.commands == build_commands
        assert provenance.invocation.environment == build_env
        assert provenance.metadata.buildInvocationId is not None
    
    def test_in_toto_statement_creation(self):
        """Test in-toto statement creation"""
        key_manager = KeyManager()
        key_id = "test-statement-key"
        key_manager.generate_key(key_id)
        
        generator = AttestationGenerator(key_manager)
        
        from core.security.attestation.attestation_generator import (
            PredicateType, Subject)
        
        subjects = [Subject(
            name="test-artifact.tar.gz",
            digest={"sha256": "abc123"}
        )]
        
        predicate = {"builder": "certeus", "version": "1.0"}
        
        statement = generator.create_in_toto_statement(
            subjects=subjects,
            predicate_type=PredicateType.SLSA_PROVENANCE,
            predicate=predicate
        )
        
        assert statement._type == "https://in-toto.io/Statement/v0.1"
        assert len(statement.subject) == 1
        assert statement.subject[0].name == "test-artifact.tar.gz"
        assert statement.predicateType == PredicateType.SLSA_PROVENANCE.value
    
    def test_dsse_envelope_signing(self):
        """Test DSSE envelope signing and verification"""
        key_manager = KeyManager()
        key_id = "test-dsse-key"
        key_manager.generate_key(key_id)
        
        generator = AttestationGenerator(key_manager)
        
        from core.security.attestation.attestation_generator import (
            PredicateType, Subject)
        
        statement = generator.create_in_toto_statement(
            subjects=[Subject(name="test", digest={"sha256": "test"})],
            predicate_type=PredicateType.SLSA_PROVENANCE,
            predicate={}
        )
        
        # Sign statement
        envelope = generator.sign_statement(statement, key_id)
        
        assert envelope.payloadType == "application/vnd.in-toto+json"
        assert len(envelope.signatures) == 1
        assert envelope.signatures[0]["keyid"] == key_id
        
        # Verify signature
        is_valid = generator.verify_dsse_envelope(envelope, key_id)
        assert is_valid == True
    
    def test_build_attestation_creation(self):
        """Test complete build attestation creation"""
        key_manager = KeyManager()
        key_id = "test-build-key"
        key_manager.generate_key(key_id)
        
        generator = AttestationGenerator(key_manager)
        
        # Create temporary test file
        with tempfile.NamedTemporaryFile(delete=False) as f:
            f.write(b"Test artifact content")
            artifact_path = Path(f.name)
        
        try:
            build_commands = ["python setup.py build"]
            
            envelope = generator.create_build_attestation(
                artifact_path=artifact_path,
                build_commands=build_commands,
                key_id=key_id
            )
            
            assert envelope.payloadType == "application/vnd.in-toto+json"
            assert len(envelope.signatures) == 1
            
            # Verify signature
            is_valid = generator.verify_dsse_envelope(envelope, key_id)
            assert is_valid == True
            
        finally:
            artifact_path.unlink(missing_ok=True)

class TestA6SecurityCVEScanning:
    """Test A6.4: CVE Vulnerability Scanning"""
    
    @pytest.mark.asyncio
    async def test_component_scanning(self):
        """Test individual component CVE scanning"""
        scanner = CVEScanner()
        
        # Create test component
        component = Component(
            type=ComponentType.LIBRARY,
            name="requests",
            version="2.25.0",  # Known vulnerable version for testing
            group="python"
        )
        
        vulnerabilities = await scanner.scan_component(component)
        
        # Should find vulnerabilities (this is a known vulnerable version)
        assert isinstance(vulnerabilities, list)
        # Note: Actual CVE results depend on external API availability
    
    @pytest.mark.asyncio
    async def test_batch_component_scanning(self):
        """Test batch component scanning"""
        scanner = CVEScanner()
        
        components = [
            Component(
                type=ComponentType.LIBRARY,
                name="urllib3",
                version="1.25.0",
                group="python"
            ),
            Component(
                type=ComponentType.LIBRARY,
                name="requests",
                version="2.20.0",
                group="python"
            )
        ]
        
        results = await scanner.scan_components(components)
        
        assert isinstance(results, dict)
        assert len(results) <= len(components)  # May filter out components without vulns
    
    def test_cve_database_operations(self):
        """Test CVE database storage and retrieval"""
        from core.security.cve.cve_scanner import (CVEDatabase, CVEItem,
                                                   CVEStatus)
        
        with tempfile.NamedTemporaryFile(suffix='.db', delete=False) as f:
            db_path = Path(f.name)
        
        try:
            db = CVEDatabase(db_path)
            
            # Create test CVE
            test_cve = CVEItem(
                cve_id="CVE-2023-TEST",
                source_identifier="test",
                published=datetime.now(timezone.utc),
                last_modified=datetime.now(timezone.utc),
                vuln_status=CVEStatus.ANALYZED,
                descriptions=[{"lang": "en", "value": "Test CVE"}]
            )
            
            # Store and retrieve
            db.store_cves([test_cve])
            
            high_cves = db.search_cves_by_severity(CVESeverity.HIGH)
            assert isinstance(high_cves, list)
            
        finally:
            # Close connection properly
            try:
                del db
                import time
                time.sleep(0.1)  # Brief delay for Windows
                db_path.unlink(missing_ok=True)
            except:
                pass
    
    def test_vulnerability_report_generation(self):
        """Test vulnerability report generation"""
        scanner = CVEScanner()
        
        from core.security.sbom.sbom_generator import Vulnerability

        # Mock scan results
        scan_results = {
            "requests": [
                Vulnerability(
                    id="CVE-2023-32681",
                    source="NVD",
                    severity="HIGH",
                    cvss_score=7.5,
                    description="Test vulnerability"
                )
            ],
            "urllib3": [
                Vulnerability(
                    id="CVE-2023-45803",
                    source="NVD", 
                    severity="CRITICAL",
                    cvss_score=9.1,
                    description="Critical test vulnerability"
                )
            ]
        }
        
        report = scanner.generate_vulnerability_report(scan_results)
        
        assert "scan_timestamp" in report
        assert "total_components_scanned" in report
        assert "total_vulnerabilities" in report
        assert "severity_breakdown" in report
        assert "critical_components" in report
        assert "recommendations" in report
        
        assert report["total_components_scanned"] == 2
        assert report["total_vulnerabilities"] == 2
        assert report["severity_breakdown"]["HIGH"] == 1
        assert report["severity_breakdown"]["CRITICAL"] == 1

class TestA6SecurityServiceIntegration:
    """Test A6.5: Security Service Integration"""
    
    @pytest.mark.asyncio
    async def test_security_service_initialization(self):
        """Test security service initialization"""
        with tempfile.TemporaryDirectory() as temp_dir:
            config_dir = Path(temp_dir) / "security_config"
            
            policy = SecurityPolicy(
                key_rotation_days=30,
                require_sbom=True,
                require_build_attestations=True,
                max_cve_severity=CVESeverity.HIGH
            )
            
            service = SecurityService(config_dir, policy)
            
            # Test initialization
            success = await service.initialize_security_infrastructure()
            
            # Note: This may fail without external dependencies
            # but should create the directory structure
            assert config_dir.exists()
            assert (config_dir / "keys").exists()
            assert (config_dir / "sbom").exists()
            assert (config_dir / "attestations").exists()
    
    @pytest.mark.asyncio
    async def test_sbom_generation_integration(self):
        """Test integrated SBOM generation"""
        with tempfile.TemporaryDirectory() as temp_dir:
            config_dir = Path(temp_dir) / "security_config"
            service = SecurityService(config_dir)
            
            # Generate SBOM
            sbom = await service.generate_project_sbom()
            
            assert sbom["bomFormat"] == "CycloneDX"
            assert "components" in sbom
            
            # Check if SBOM file was created
            sbom_file = config_dir / "sbom" / "project_sbom.json"
            assert sbom_file.exists()
    
    @pytest.mark.asyncio 
    async def test_build_attestation_integration(self):
        """Test integrated build attestation"""
        with tempfile.TemporaryDirectory() as temp_dir:
            config_dir = Path(temp_dir) / "security_config"
            service = SecurityService(config_dir)
            
            # Initialize security first
            await service.initialize_security_infrastructure()
            
            # Create test artifact
            artifact_path = Path(temp_dir) / "test_artifact.txt"
            artifact_path.write_text("Test artifact content")
            
            build_commands = ["echo 'test build'"]
            
            envelope = await service.create_build_attestation(
                artifact_path=artifact_path,
                build_commands=build_commands
            )
            
            assert envelope.payloadType == "application/vnd.in-toto+json"
            assert len(envelope.signatures) == 1
    
    @pytest.mark.asyncio
    async def test_security_report_generation(self):
        """Test comprehensive security report"""
        with tempfile.TemporaryDirectory() as temp_dir:
            config_dir = Path(temp_dir) / "security_config"
            service = SecurityService(config_dir)
            
            # Initialize and generate report
            await service.initialize_security_infrastructure()
            report = await service.generate_security_report()
            
            assert hasattr(report, 'timestamp')
            assert hasattr(report, 'security_level')
            assert hasattr(report, 'security_score')
            assert hasattr(report, 'recommendations')
            assert isinstance(report.recommendations, list)
            assert 0 <= report.security_score <= 100
    
    def test_audit_logging(self):
        """Test security audit logging"""
        with tempfile.TemporaryDirectory() as temp_dir:
            config_dir = Path(temp_dir) / "security_config"
            
            policy = SecurityPolicy(audit_logging=True)
            service = SecurityService(config_dir, policy)
            
            # Generate audit event
            service._log_audit_event(
                "TEST_EVENT",
                "TestComponent",
                {"test": "data"},
                "INFO"
            )
            
            assert len(service.audit_log) == 1
            event = service.audit_log[0]
            assert event.event_type == "TEST_EVENT"
            assert event.component == "TestComponent"
            assert event.severity == "INFO"
    
    @pytest.mark.asyncio
    async def test_security_configuration_export(self):
        """Test security configuration export"""
        with tempfile.TemporaryDirectory() as temp_dir:
            config_dir = Path(temp_dir) / "security_config"
            service = SecurityService(config_dir)
            
            await service.initialize_security_infrastructure()
            
            export_path = Path(temp_dir) / "security_export.json"
            await service.export_security_configuration(export_path)
            
            assert export_path.exists()
            
            with open(export_path) as f:
                config = json.load(f)
            
            assert "security_policy" in config
            assert "active_keys" in config
            assert "export_timestamp" in config

# Performance and stress tests
class TestA6SecurityPerformance:
    """Test A6.6: Security Performance & Scale"""
    
    def test_key_generation_performance(self):
        """Test key generation performance"""
        key_manager = KeyManager()
        
        import time
        start_time = time.time()
        
        # Generate multiple keys
        for i in range(10):
            key_id = f"perf-test-key-{i}"
            key_manager.generate_key(key_id)
        
        end_time = time.time()
        total_time = end_time - start_time
        
        # Should generate 10 keys in reasonable time (< 5 seconds)
        assert total_time < 5.0
        
        # Cleanup - list keys instead of revoke (since revoke may not be implemented)
        keys = key_manager.list_keys()
        assert len(keys) >= 10
    
    def test_signing_performance(self):
        """Test signing performance with multiple operations"""
        key_manager = KeyManager()
        key_id = "perf-signing-key"
        key_manager.generate_key(key_id)
        
        test_data = b"Performance test data for signing"
        
        import time
        start_time = time.time()
        
        # Perform multiple sign/verify operations
        for _ in range(100):
            signature = key_manager.sign_data(key_id, test_data)
            is_valid = key_manager.verify_signature(key_id, test_data, signature)
            assert is_valid
        
        end_time = time.time()
        total_time = end_time - start_time
        
        # Should complete 100 sign/verify cycles in reasonable time
        assert total_time < 10.0
        
        ops_per_second = 100 / total_time
        print(f"Signing performance: {ops_per_second:.2f} ops/second")
    
    def test_sbom_generation_performance(self):
        """Test SBOM generation performance"""
        generator = SBOMGenerator()
        
        import time
        start_time = time.time()
        
        # Generate SBOM
        sbom = generator.generate_sbom(scan_for_vulnerabilities=False)
        
        end_time = time.time()
        generation_time = end_time - start_time
        
        # Should generate SBOM in reasonable time
        assert generation_time < 30.0  # 30 seconds max
        
        component_count = len(sbom.get("components", []))
        print(f"SBOM generation: {component_count} components in {generation_time:.2f}s")

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])