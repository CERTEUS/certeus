# CERTEUS Engine - A6 Security SBOM Generator
# Quantum-Resistance Temporal & Security Protocol
# SBOM: CycloneDX format with CVE scanning integration

from dataclasses import dataclass, field
from datetime import UTC, datetime
from enum import Enum
import hashlib
import json
import logging
from pathlib import Path
from typing import Any
import uuid
import warnings

warnings.filterwarnings("ignore", category=UserWarning, message="pkg_resources is deprecated.*")

# Must import after warnings filter due to deprecation warnings
try:
    import pkg_resources
except ImportError:
    pkg_resources = None

logger = logging.getLogger(__name__)


class ComponentType(Enum):
    """CycloneDX component types"""

    APPLICATION = "application"
    FRAMEWORK = "framework"
    LIBRARY = "library"
    CONTAINER = "container"
    OPERATING_SYSTEM = "operating-system"
    DEVICE = "device"
    FIRMWARE = "firmware"
    FILE = "file"


class HashAlgorithm(Enum):
    """Supported hash algorithms for integrity verification"""

    SHA1 = "SHA-1"
    SHA256 = "SHA-256"
    SHA512 = "SHA-512"
    MD5 = "MD5"


@dataclass
class ComponentHash:
    """Component integrity hash"""

    algorithm: HashAlgorithm
    value: str


@dataclass
class ExternalReference:
    """External reference for component"""

    type: str  # vcs, website, documentation, etc.
    url: str
    comment: str | None = None


@dataclass
class License:
    """License information"""

    license_id: str | None = None  # SPDX license ID
    license_name: str | None = None
    license_text: str | None = None
    license_url: str | None = None


@dataclass
class Vulnerability:
    """CVE vulnerability information"""

    id: str  # CVE-2023-1234
    source: str  # NVD, GitHub, etc.
    severity: str  # LOW, MEDIUM, HIGH, CRITICAL
    cvss_score: float | None = None
    description: str | None = None
    recommendation: str | None = None
    published: datetime | None = None
    updated: datetime | None = None


@dataclass
class Component:
    """CycloneDX software component"""

    type: ComponentType
    name: str
    version: str
    bom_ref: str = field(default_factory=lambda: str(uuid.uuid4()))
    supplier: str | None = None
    author: str | None = None
    publisher: str | None = None
    group: str | None = None  # namespace/organization
    description: str | None = None
    scope: str = "required"  # required, optional, excluded
    hashes: list[ComponentHash] = field(default_factory=list)
    licenses: list[License] = field(default_factory=list)
    copyright: str | None = None
    cpe: str | None = None  # Common Platform Enumeration
    purl: str | None = None  # Package URL
    external_references: list[ExternalReference] = field(default_factory=list)
    vulnerabilities: list[Vulnerability] = field(default_factory=list)


class SBOMGenerator:
    """
    Software Bill of Materials (SBOM) generator using CycloneDX format

    Features:
    - Python package dependency analysis
    - CycloneDX 1.4 JSON format
    - CVE vulnerability scanning integration
    - License detection and SPDX mapping
    - Component integrity hashing
    - Supply chain provenance tracking
    """

    def __init__(self, project_path: Path | None = None):
        self.project_path = project_path or Path.cwd()
        self.components: list[Component] = []
        self.metadata = {
            "timestamp": datetime.now(UTC),
            "tools": ["certeus-sbom-generator"],
            "authors": [{"name": "CERTEUS Security Team"}],
        }

    def analyze_python_dependencies(self) -> list[Component]:
        """Analyze Python dependencies from installed packages"""

        components = []

        try:
            # Get installed packages
            installed_packages = [d for d in pkg_resources.working_set]

            for package in installed_packages:
                component = self._create_python_component(package)
                if component:
                    components.append(component)

        except Exception as e:
            logger.error(f"Error analyzing Python dependencies: {e}")

        return components

    def _create_python_component(self, package: pkg_resources.Distribution) -> Component | None:
        """Create CycloneDX component from Python package"""

        try:
            # Basic component info
            component = Component(
                type=ComponentType.LIBRARY,
                name=package.project_name,
                version=package.version,
                group="python",
                description=self._get_package_description(package),
                purl=f"pkg:pypi/{package.project_name}@{package.version}",
            )

            # Add license information
            license_info = self._get_package_license(package)
            if license_info:
                component.licenses.append(license_info)

            # Add external references
            component.external_references = self._get_package_references(package)

            # Add hash if available
            if hasattr(package, 'location') and package.location:
                package_hash = self._calculate_package_hash(package.location)
                if package_hash:
                    component.hashes.append(package_hash)

            return component

        except Exception as e:
            logger.warning(f"Failed to create component for {package.project_name}: {e}")
            return None

    def _get_package_description(self, package: pkg_resources.Distribution) -> str | None:
        """Get package description from metadata"""
        try:
            if hasattr(package, '_dep_map'):
                metadata = package.get_metadata('METADATA')
                for line in metadata.split('\n'):
                    if line.startswith('Summary:'):
                        return line.split(':', 1)[1].strip()
        except:
            pass
        return None

    def _get_package_license(self, package: pkg_resources.Distribution) -> License | None:
        """Extract license information from package metadata"""
        try:
            if hasattr(package, '_dep_map'):
                metadata = package.get_metadata('METADATA')
                for line in metadata.split('\n'):
                    if line.startswith('License:'):
                        license_text = line.split(':', 1)[1].strip()

                        # Map common licenses to SPDX IDs
                        spdx_mapping = {
                            'MIT': 'MIT',
                            'Apache 2.0': 'Apache-2.0',
                            'Apache Software License': 'Apache-2.0',
                            'BSD': 'BSD-3-Clause',
                            'GPL v3': 'GPL-3.0',
                            'GPL-3.0': 'GPL-3.0',
                            'LGPL': 'LGPL-2.1',
                        }

                        license_id = spdx_mapping.get(license_text)

                        return License(license_id=license_id, license_name=license_text)
        except:
            pass
        return None

    def _get_package_references(self, package: pkg_resources.Distribution) -> list[ExternalReference]:
        """Get external references for package"""
        references = []

        try:
            if hasattr(package, '_dep_map'):
                metadata = package.get_metadata('METADATA')
                for line in metadata.split('\n'):
                    if line.startswith('Home-page:'):
                        url = line.split(':', 1)[1].strip()
                        references.append(ExternalReference(type="website", url=url))
                    elif line.startswith('Download-URL:'):
                        url = line.split(':', 1)[1].strip()
                        references.append(ExternalReference(type="distribution", url=url))
        except:
            pass

        # Add PyPI reference
        references.append(
            ExternalReference(
                type="distribution", url=f"https://pypi.org/project/{package.project_name}/{package.version}/"
            )
        )

        return references

    def _calculate_package_hash(self, location: str) -> ComponentHash | None:
        """Calculate hash for package integrity verification"""
        try:
            # For wheel files, calculate SHA-256
            location_path = Path(location)
            if location_path.is_file() and location_path.suffix == '.whl':
                with open(location_path, 'rb') as f:
                    content = f.read()
                    sha256_hash = hashlib.sha256(content).hexdigest()
                    return ComponentHash(algorithm=HashAlgorithm.SHA256, value=sha256_hash)
        except Exception as e:
            logger.debug(f"Failed to calculate hash for {location}: {e}")

        return None

    def scan_vulnerabilities(self, component: Component) -> list[Vulnerability]:
        """
        Scan component for known vulnerabilities

        In production, this would integrate with:
        - NIST NVD API
        - GitHub Advisory Database
        - OSV (Open Source Vulnerabilities)
        - Snyk, FOSSA, or similar services
        """

        vulnerabilities = []

        # Mock CVE scanning for demonstration
        # In real implementation, would call external vulnerability databases
        if component.type == ComponentType.LIBRARY and component.group == "python":
            # Example: check against known vulnerable packages
            known_vulnerable = {
                'requests': [
                    Vulnerability(
                        id="CVE-2023-32681",
                        source="NVD",
                        severity="MEDIUM",
                        cvss_score=6.1,
                        description="Requests library vulnerable to proxy tunnel injection",
                        recommendation="Upgrade to requests >= 2.31.0",
                    )
                ],
                'urllib3': [
                    Vulnerability(
                        id="CVE-2023-45803",
                        source="NVD",
                        severity="HIGH",
                        cvss_score=4.2,
                        description="urllib3 Cookie header injection vulnerability",
                        recommendation="Upgrade to urllib3 >= 2.0.7",
                    )
                ],
            }

            if component.name.lower() in known_vulnerable:
                vulnerabilities.extend(known_vulnerable[component.name.lower()])

        return vulnerabilities

    def generate_sbom(
        self, include_dev_dependencies: bool = False, scan_for_vulnerabilities: bool = True
    ) -> dict[str, Any]:
        """
        Generate complete SBOM in CycloneDX format

        Args:
            include_dev_dependencies: Include development dependencies
            scan_for_vulnerabilities: Perform vulnerability scanning

        Returns:
            CycloneDX SBOM dictionary
        """

        # Analyze dependencies
        logger.info("Analyzing Python dependencies...")
        python_components = self.analyze_python_dependencies()

        # Scan for vulnerabilities if requested
        if scan_for_vulnerabilities:
            logger.info("Scanning for vulnerabilities...")
            for component in python_components:
                component.vulnerabilities = self.scan_vulnerabilities(component)

        # Create main application component
        main_component = Component(
            type=ComponentType.APPLICATION,
            name="certeus-engine",
            version="1.0.0",
            group="certeus",
            description="CERTEUS Quantum-Resistance Engine",
            author="CERTEUS Team",
        )

        # Build component list
        all_components = [main_component] + python_components

        # Generate CycloneDX SBOM
        sbom = {
            "bomFormat": "CycloneDX",
            "specVersion": "1.4",
            "serialNumber": f"urn:uuid:{uuid.uuid4()}",
            "version": 1,
            "metadata": {
                "timestamp": self.metadata["timestamp"].isoformat(),
                "tools": [{"vendor": "CERTEUS", "name": "certeus-sbom-generator", "version": "1.0.0"}],
                "authors": self.metadata["authors"],
                "component": self._component_to_dict(main_component),
            },
            "components": [self._component_to_dict(comp) for comp in python_components],
        }

        # Add vulnerabilities section if any found
        all_vulns = []
        for component in all_components:
            for vuln in component.vulnerabilities:
                vuln_dict = {
                    "id": vuln.id,
                    "source": {"name": vuln.source},
                    "ratings": [{"severity": vuln.severity, "score": vuln.cvss_score}] if vuln.cvss_score else [],
                    "description": vuln.description,
                    "recommendation": vuln.recommendation,
                    "affects": [{"ref": component.bom_ref}],
                }
                if vuln.published:
                    vuln_dict["published"] = vuln.published.isoformat()
                if vuln.updated:
                    vuln_dict["updated"] = vuln.updated.isoformat()

                all_vulns.append(vuln_dict)

        if all_vulns:
            sbom["vulnerabilities"] = all_vulns

        logger.info(f"Generated SBOM with {len(python_components)} components, {len(all_vulns)} vulnerabilities")
        return sbom

    def _component_to_dict(self, component: Component) -> dict[str, Any]:
        """Convert Component to CycloneDX dictionary format"""

        comp_dict = {
            "type": component.type.value,
            "bom-ref": component.bom_ref,
            "name": component.name,
            "version": component.version,
        }

        if component.group:
            comp_dict["group"] = component.group
        if component.description:
            comp_dict["description"] = component.description
        if component.supplier:
            comp_dict["supplier"] = {"name": component.supplier}
        if component.author:
            comp_dict["author"] = component.author
        if component.publisher:
            comp_dict["publisher"] = component.publisher
        if component.copyright:
            comp_dict["copyright"] = component.copyright
        if component.purl:
            comp_dict["purl"] = component.purl
        if component.cpe:
            comp_dict["cpe"] = component.cpe

        if component.scope != "required":
            comp_dict["scope"] = component.scope

        # Add hashes
        if component.hashes:
            comp_dict["hashes"] = [
                {"alg": hash_obj.algorithm.value, "content": hash_obj.value} for hash_obj in component.hashes
            ]

        # Add licenses
        if component.licenses:
            licenses = []
            for license_obj in component.licenses:
                license_dict = {}
                if license_obj.license_id:
                    license_dict["license"] = {"id": license_obj.license_id}
                elif license_obj.license_name:
                    license_dict["license"] = {"name": license_obj.license_name}
                if license_obj.license_text:
                    license_dict["license"]["text"] = {"content": license_obj.license_text}
                if license_obj.license_url:
                    license_dict["license"]["url"] = license_obj.license_url
                licenses.append(license_dict)
            comp_dict["licenses"] = licenses

        # Add external references
        if component.external_references:
            comp_dict["externalReferences"] = [
                {"type": ref.type, "url": ref.url, "comment": ref.comment}
                if ref.comment
                else {"type": ref.type, "url": ref.url}
                for ref in component.external_references
            ]

        return comp_dict

    def save_sbom(self, sbom: dict[str, Any], output_path: Path):
        """Save SBOM to file"""

        with open(output_path, 'w') as f:
            json.dump(sbom, f, indent=2, default=str)

        logger.info(f"SBOM saved to {output_path}")

    def validate_sbom(self, sbom: dict[str, Any]) -> list[str]:
        """Validate SBOM against CycloneDX schema"""

        validation_errors = []

        # Basic structure validation
        required_fields = ["bomFormat", "specVersion", "serialNumber", "version", "metadata"]
        for required_field in required_fields:
            if required_field not in sbom:
                validation_errors.append(f"Missing required field: {required_field}")

        # Format validation
        if sbom.get("bomFormat") != "CycloneDX":
            validation_errors.append("Invalid bomFormat, must be 'CycloneDX'")

        # Component validation
        if "components" in sbom:
            for i, component in enumerate(sbom["components"]):
                if "name" not in component:
                    validation_errors.append(f"Component {i} missing required 'name' field")
                if "version" not in component:
                    validation_errors.append(f"Component {i} missing required 'version' field")

        return validation_errors

    def get_vulnerability_summary(self, sbom: dict[str, Any]) -> dict[str, int]:
        """Get vulnerability count summary by severity"""

        summary = {"CRITICAL": 0, "HIGH": 0, "MEDIUM": 0, "LOW": 0}

        if "vulnerabilities" in sbom:
            for vuln in sbom["vulnerabilities"]:
                if "ratings" in vuln and vuln["ratings"]:
                    severity = vuln["ratings"][0].get("severity", "UNKNOWN")
                    if severity in summary:
                        summary[severity] += 1

        return summary
