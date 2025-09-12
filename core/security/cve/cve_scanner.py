# CERTEUS Engine - A6 Security CVE Scanner
# Quantum-Resistance Temporal & Security Protocol
# CVE vulnerability scanning with NIST NVD integration

import asyncio
from dataclasses import dataclass, field
from datetime import UTC, datetime, timedelta
from enum import Enum
import json
import logging
from pathlib import Path
import re
import sqlite3
from typing import Any

import aiohttp
from packaging import version

from ..sbom.sbom_generator import Component, ComponentType, Vulnerability

logger = logging.getLogger(__name__)

class CVESeverity(Enum):
    """CVE Severity levels"""
    NONE = "NONE"
    LOW = "LOW"
    MEDIUM = "MEDIUM"
    HIGH = "HIGH"
    CRITICAL = "CRITICAL"

class CVEStatus(Enum):
    """CVE Status in database"""
    ANALYZED = "Analyzed"
    MODIFIED = "Modified"
    AWAITING_ANALYSIS = "Awaiting Analysis"
    UNDERGOING_ANALYSIS = "Undergoing Analysis"
    REJECTED = "Rejected"

@dataclass
class CPEMatch:
    """Common Platform Enumeration match"""
    vulnerable: bool
    criteria: str  # CPE 2.3 string
    version_start_including: str | None = None
    version_start_excluding: str | None = None
    version_end_including: str | None = None
    version_end_excluding: str | None = None

@dataclass
class CVSSScore:
    """CVSS scoring information"""
    version: str  # "3.1", "2.0"
    vector_string: str  # CVSS vector
    base_score: float
    temporal_score: float | None = None
    environmental_score: float | None = None
    base_severity: str | None = None
    exploitability_score: float | None = None
    impact_score: float | None = None

@dataclass
class CVEReference:
    """CVE external reference"""
    url: str
    source: str
    tags: list[str] = field(default_factory=list)

@dataclass
class CVEItem:
    """Complete CVE vulnerability item"""
    cve_id: str
    source_identifier: str
    published: datetime
    last_modified: datetime
    vuln_status: CVEStatus
    descriptions: list[dict[str, str]]  # lang -> description
    references: list[CVEReference] = field(default_factory=list)
    cvss_v3: CVSSScore | None = None
    cvss_v2: CVSSScore | None = None
    cpe_matches: list[CPEMatch] = field(default_factory=list)
    weaknesses: list[str] = field(default_factory=list)  # CWE IDs
    configurations: list[dict[str, Any]] = field(default_factory=list)

class NISTNVDClient:
    """NIST National Vulnerability Database API client"""
    
    BASE_URL = "https://services.nvd.nist.gov/rest/json/cves/2.0"
    
    def __init__(self, api_key: str | None = None, rate_limit: float = 0.6):
        self.api_key = api_key
        self.rate_limit = rate_limit  # seconds between requests
        self.session: aiohttp.ClientSession | None = None
        
        # Headers
        self.headers = {
            "User-Agent": "CERTEUS-CVE-Scanner/1.0",
            "Accept": "application/json"
        }
        if api_key:
            self.headers["apiKey"] = api_key
    
    async def __aenter__(self):
        """Async context manager entry"""
        self.session = aiohttp.ClientSession(headers=self.headers)
        return self
    
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit"""
        if self.session:
            await self.session.close()
    
    async def search_cves(self,
                         cpe_name: str | None = None,
                         keyword: str | None = None,
                         last_mod_start_date: datetime | None = None,
                         last_mod_end_date: datetime | None = None,
                         pub_start_date: datetime | None = None,
                         pub_end_date: datetime | None = None,
                         cvss_v3_severity: CVESeverity | None = None,
                         results_per_page: int = 100) -> list[CVEItem]:
        """Search CVEs in NIST NVD"""
        
        if not self.session:
            raise RuntimeError("Client not initialized. Use async context manager.")
        
        params = {
            "resultsPerPage": min(results_per_page, 2000)
        }
        
        if cpe_name:
            params["cpeName"] = cpe_name
        if keyword:
            params["keywordSearch"] = keyword
        if last_mod_start_date:
            params["lastModStartDate"] = last_mod_start_date.isoformat()
        if last_mod_end_date:
            params["lastModEndDate"] = last_mod_end_date.isoformat()
        if pub_start_date:
            params["pubStartDate"] = pub_start_date.isoformat()
        if pub_end_date:
            params["pubEndDate"] = pub_end_date.isoformat()
        if cvss_v3_severity:
            params["cvssV3Severity"] = cvss_v3_severity.value
        
        all_cves = []
        start_index = 0
        
        while True:
            params["startIndex"] = start_index
            
            try:
                # Rate limiting
                await asyncio.sleep(self.rate_limit)
                
                async with self.session.get(self.BASE_URL, params=params) as response:
                    if response.status == 200:
                        data = await response.json()
                        
                        cves = self._parse_cves(data.get("vulnerabilities", []))
                        all_cves.extend(cves)
                        
                        # Check if more results available
                        total_results = data.get("totalResults", 0)
                        if start_index + len(cves) >= total_results:
                            break
                        
                        start_index += results_per_page
                    else:
                        logger.error(f"NVD API error: {response.status}")
                        break
                        
            except Exception as e:
                logger.error(f"Error fetching CVEs: {e}")
                break
        
        logger.info(f"Retrieved {len(all_cves)} CVEs from NVD")
        return all_cves
    
    def _parse_cves(self, vulnerabilities: list[dict[str, Any]]) -> list[CVEItem]:
        """Parse CVE data from NVD API response"""
        
        cves = []
        
        for vuln_data in vulnerabilities:
            try:
                cve_data = vuln_data.get("cve", {})
                
                # Basic CVE info
                cve_id = cve_data.get("id", "")
                source_identifier = cve_data.get("sourceIdentifier", "")
                published = datetime.fromisoformat(cve_data.get("published", "").replace("Z", "+00:00"))
                last_modified = datetime.fromisoformat(cve_data.get("lastModified", "").replace("Z", "+00:00"))
                vuln_status = CVEStatus(cve_data.get("vulnStatus", "Analyzed"))
                
                # Descriptions
                descriptions = []
                for desc in cve_data.get("descriptions", []):
                    descriptions.append({
                        "lang": desc.get("lang", "en"),
                        "value": desc.get("value", "")
                    })
                
                # References
                references = []
                for ref in cve_data.get("references", []):
                    references.append(CVEReference(
                        url=ref.get("url", ""),
                        source=ref.get("source", ""),
                        tags=ref.get("tags", [])
                    ))
                
                # CVSS scores
                cvss_v3 = None
                cvss_v2 = None
                
                metrics = cve_data.get("metrics", {})
                
                # CVSS v3.x
                if "cvssMetricV31" in metrics or "cvssMetricV30" in metrics:
                    cvss_key = "cvssMetricV31" if "cvssMetricV31" in metrics else "cvssMetricV30"
                    cvss_metrics = metrics[cvss_key][0].get("cvssData", {})
                    
                    cvss_v3 = CVSSScore(
                        version=cvss_metrics.get("version", "3.1"),
                        vector_string=cvss_metrics.get("vectorString", ""),
                        base_score=cvss_metrics.get("baseScore", 0.0),
                        base_severity=cvss_metrics.get("baseSeverity"),
                        exploitability_score=metrics[cvss_key][0].get("exploitabilityScore"),
                        impact_score=metrics[cvss_key][0].get("impactScore")
                    )
                
                # CVSS v2
                if "cvssMetricV2" in metrics:
                    cvss_metrics = metrics["cvssMetricV2"][0].get("cvssData", {})
                    
                    cvss_v2 = CVSSScore(
                        version="2.0",
                        vector_string=cvss_metrics.get("vectorString", ""),
                        base_score=cvss_metrics.get("baseScore", 0.0),
                        exploitability_score=metrics["cvssMetricV2"][0].get("exploitabilityScore"),
                        impact_score=metrics["cvssMetricV2"][0].get("impactScore")
                    )
                
                # CPE configurations
                cpe_matches = []
                configurations = cve_data.get("configurations", [])
                
                for config in configurations:
                    for node in config.get("nodes", []):
                        for cpe_match in node.get("cpeMatch", []):
                            cpe_matches.append(CPEMatch(
                                vulnerable=cpe_match.get("vulnerable", False),
                                criteria=cpe_match.get("criteria", ""),
                                version_start_including=cpe_match.get("versionStartIncluding"),
                                version_start_excluding=cpe_match.get("versionStartExcluding"),
                                version_end_including=cpe_match.get("versionEndIncluding"),
                                version_end_excluding=cpe_match.get("versionEndExcluding")
                            ))
                
                # Weaknesses (CWE)
                weaknesses = []
                for weakness in cve_data.get("weaknesses", []):
                    for desc in weakness.get("description", []):
                        if desc.get("lang") == "en":
                            weaknesses.append(desc.get("value", ""))
                
                cve_item = CVEItem(
                    cve_id=cve_id,
                    source_identifier=source_identifier,
                    published=published,
                    last_modified=last_modified,
                    vuln_status=vuln_status,
                    descriptions=descriptions,
                    references=references,
                    cvss_v3=cvss_v3,
                    cvss_v2=cvss_v2,
                    cpe_matches=cpe_matches,
                    weaknesses=weaknesses,
                    configurations=configurations
                )
                
                cves.append(cve_item)
                
            except Exception as e:
                logger.warning(f"Failed to parse CVE: {e}")
                continue
        
        return cves

class CVEDatabase:
    """Local SQLite database for CVE caching and management"""
    
    def __init__(self, db_path: Path):
        self.db_path = db_path
        self._ensure_database()
    
    def _ensure_database(self):
        """Create database tables if not exist"""
        
        with sqlite3.connect(self.db_path) as conn:
            conn.executescript("""
            CREATE TABLE IF NOT EXISTS cves (
                id TEXT PRIMARY KEY,
                source_identifier TEXT,
                published TEXT,
                last_modified TEXT,
                vuln_status TEXT,
                description TEXT,
                cvss_v3_score REAL,
                cvss_v3_severity TEXT,
                cvss_v2_score REAL,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP
            );
            
            CREATE TABLE IF NOT EXISTS cve_references (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                cve_id TEXT,
                url TEXT,
                source TEXT,
                tags TEXT,
                FOREIGN KEY (cve_id) REFERENCES cves (id)
            );
            
            CREATE TABLE IF NOT EXISTS cpe_matches (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                cve_id TEXT,
                vulnerable INTEGER,
                criteria TEXT,
                version_start_including TEXT,
                version_start_excluding TEXT,
                version_end_including TEXT,
                version_end_excluding TEXT,
                FOREIGN KEY (cve_id) REFERENCES cves (id)
            );
            
            CREATE TABLE IF NOT EXISTS component_scans (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                component_name TEXT,
                component_version TEXT,
                scan_date TEXT,
                vulnerabilities_found INTEGER,
                scan_hash TEXT
            );
            
            CREATE INDEX IF NOT EXISTS idx_cves_published ON cves (published);
            CREATE INDEX IF NOT EXISTS idx_cves_severity ON cves (cvss_v3_severity);
            CREATE INDEX IF NOT EXISTS idx_cpe_criteria ON cpe_matches (criteria);
            """)
    
    def store_cves(self, cves: list[CVEItem]):
        """Store CVEs in database"""
        
        with sqlite3.connect(self.db_path) as conn:
            for cve in cves:
                # Main CVE record
                description = ""
                for desc in cve.descriptions:
                    if desc.get("lang") == "en":
                        description = desc.get("value", "")
                        break
                
                cvss_v3_score = cve.cvss_v3.base_score if cve.cvss_v3 else None
                cvss_v3_severity = cve.cvss_v3.base_severity if cve.cvss_v3 else None
                cvss_v2_score = cve.cvss_v2.base_score if cve.cvss_v2 else None
                
                conn.execute("""
                INSERT OR REPLACE INTO cves 
                (id, source_identifier, published, last_modified, vuln_status, 
                 description, cvss_v3_score, cvss_v3_severity, cvss_v2_score)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    cve.cve_id,
                    cve.source_identifier,
                    cve.published.isoformat(),
                    cve.last_modified.isoformat(),
                    cve.vuln_status.value,
                    description,
                    cvss_v3_score,
                    cvss_v3_severity,
                    cvss_v2_score
                ))
                
                # References
                conn.execute("DELETE FROM cve_references WHERE cve_id = ?", (cve.cve_id,))
                for ref in cve.references:
                    conn.execute("""
                    INSERT INTO cve_references (cve_id, url, source, tags)
                    VALUES (?, ?, ?, ?)
                    """, (cve.cve_id, ref.url, ref.source, json.dumps(ref.tags)))
                
                # CPE matches
                conn.execute("DELETE FROM cpe_matches WHERE cve_id = ?", (cve.cve_id,))
                for cpe in cve.cpe_matches:
                    conn.execute("""
                    INSERT INTO cpe_matches 
                    (cve_id, vulnerable, criteria, version_start_including,
                     version_start_excluding, version_end_including, version_end_excluding)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                    """, (
                        cve.cve_id,
                        1 if cpe.vulnerable else 0,
                        cpe.criteria,
                        cpe.version_start_including,
                        cpe.version_start_excluding,
                        cpe.version_end_including,
                        cpe.version_end_excluding
                    ))
    
    def search_cves_by_severity(self, min_severity: CVESeverity) -> list[CVEItem]:
        """Search CVEs by minimum severity level"""
        
        severity_order = {
            CVESeverity.NONE: 0,
            CVESeverity.LOW: 1,
            CVESeverity.MEDIUM: 2,
            CVESeverity.HIGH: 3,
            CVESeverity.CRITICAL: 4
        }
        
        min_score = severity_order.get(min_severity, 0)
        severity_filter = []
        
        for sev, score in severity_order.items():
            if score >= min_score:
                severity_filter.append(sev.value)
        
        with sqlite3.connect(self.db_path) as conn:
            conn.row_factory = sqlite3.Row
            
            cursor = conn.execute("""
            SELECT * FROM cves 
            WHERE cvss_v3_severity IN ({})
            ORDER BY cvss_v3_score DESC
            """.format(','.join('?' * len(severity_filter))), severity_filter)
            
            return [self._row_to_cve(row) for row in cursor.fetchall()]
    
    def _row_to_cve(self, row: sqlite3.Row) -> CVEItem:
        """Convert database row to CVEItem"""
        
        return CVEItem(
            cve_id=row["id"],
            source_identifier=row["source_identifier"],
            published=datetime.fromisoformat(row["published"]),
            last_modified=datetime.fromisoformat(row["last_modified"]),
            vuln_status=CVEStatus(row["vuln_status"]),
            descriptions=[{"lang": "en", "value": row["description"]}],
            cvss_v3=CVSSScore(
                version="3.1",
                vector_string="",
                base_score=row["cvss_v3_score"] or 0.0,
                base_severity=row["cvss_v3_severity"]
            ) if row["cvss_v3_score"] else None
        )

class CVEScanner:
    """
    Enterprise CVE vulnerability scanner
    
    Features:
    - NIST NVD integration for authoritative CVE data
    - Python package vulnerability scanning
    - Component version range matching
    - Severity filtering (HIGH/CRITICAL)
    - Local database caching
    - Batch scanning optimization
    - False positive reduction
    """
    
    def __init__(self, 
                 db_path: Path | None = None,
                 nvd_api_key: str | None = None,
                 cache_duration_hours: int = 24):
        self.db_path = db_path or Path("cve_cache.db")
        self.nvd_api_key = nvd_api_key
        self.cache_duration = timedelta(hours=cache_duration_hours)
        self.db = CVEDatabase(self.db_path)
    
    async def scan_component(self, component: Component) -> list[Vulnerability]:
        """Scan single component for vulnerabilities"""
        
        vulnerabilities = []
        
        # Python package scanning
        if component.type == ComponentType.LIBRARY and component.group == "python":
            vulnerabilities.extend(await self._scan_python_package(component))
        
        return vulnerabilities
    
    async def scan_components(self, components: list[Component]) -> dict[str, list[Vulnerability]]:
        """Scan multiple components for vulnerabilities"""
        
        results = {}
        
        # Group by type for efficient batch scanning
        python_packages = [c for c in components 
                          if c.type == ComponentType.LIBRARY and c.group == "python"]
        
        # Scan Python packages
        for component in python_packages:
            results[component.name] = await self.scan_component(component)
        
        return results
    
    async def _scan_python_package(self, component: Component) -> list[Vulnerability]:
        """Scan Python package for CVEs"""
        
        package_name = component.name.lower()
        package_version = component.version
        
        vulnerabilities = []
        
        try:
            # Search for CVEs mentioning this package
            async with NISTNVDClient(api_key=self.nvd_api_key) as nvd_client:
                cves = await nvd_client.search_cves(
                    keyword=f"python {package_name}",
                    cvss_v3_severity=CVESeverity.MEDIUM,  # MEDIUM and above
                    results_per_page=50
                )
                
                # Cache CVEs
                self.db.store_cves(cves)
                
                # Filter relevant CVEs
                for cve in cves:
                    if self._is_cve_relevant(cve, package_name, package_version):
                        vulnerability = self._cve_to_vulnerability(cve)
                        vulnerabilities.append(vulnerability)
        
        except Exception as e:
            logger.error(f"Error scanning {package_name}: {e}")
        
        return vulnerabilities
    
    def _is_cve_relevant(self, cve: CVEItem, package_name: str, package_version: str) -> bool:
        """Check if CVE is relevant to package version"""
        
        # Check description for package name
        description_text = ""
        for desc in cve.descriptions:
            if desc.get("lang") == "en":
                description_text = desc.get("value", "").lower()
                break
        
        if package_name not in description_text:
            return False
        
        # Check CPE matches for version ranges
        for cpe_match in cve.cpe_matches:
            if not cpe_match.vulnerable:
                continue
            
            criteria = cpe_match.criteria.lower()
            if package_name in criteria:
                # Check version constraints
                if self._version_in_range(
                    package_version,
                    cpe_match.version_start_including,
                    cpe_match.version_start_excluding,
                    cpe_match.version_end_including,
                    cpe_match.version_end_excluding
                ):
                    return True
        
        # Fallback: check if description mentions version patterns
        version_patterns = [
            rf"{re.escape(package_name)}\s+.*?{re.escape(package_version)}",
            rf"{re.escape(package_name)}\s+version.*?{re.escape(package_version)}",
            rf"{re.escape(package_name)}\s+before\s+(\d+\.\d+)",
            rf"{re.escape(package_name)}\s+prior\s+to\s+(\d+\.\d+)"
        ]
        
        for pattern in version_patterns:
            if re.search(pattern, description_text, re.IGNORECASE):
                return True
        
        return False
    
    def _version_in_range(self,
                         target_version: str,
                         start_including: str | None,
                         start_excluding: str | None,
                         end_including: str | None,
                         end_excluding: str | None) -> bool:
        """Check if version falls within vulnerability range"""
        
        try:
            target_ver = version.parse(target_version)
            
            # Check start constraints
            if start_including:
                if target_ver < version.parse(start_including):
                    return False
            
            if start_excluding:
                if target_ver <= version.parse(start_excluding):
                    return False
            
            # Check end constraints
            if end_including:
                if target_ver > version.parse(end_including):
                    return False
            
            if end_excluding:
                if target_ver >= version.parse(end_excluding):
                    return False
            
            return True
            
        except Exception:
            # If version parsing fails, be conservative
            return True
    
    def _cve_to_vulnerability(self, cve: CVEItem) -> Vulnerability:
        """Convert CVEItem to Vulnerability"""
        
        description = ""
        for desc in cve.descriptions:
            if desc.get("lang") == "en":
                description = desc.get("value", "")
                break
        
        severity = "MEDIUM"
        cvss_score = None
        
        if cve.cvss_v3:
            severity = cve.cvss_v3.base_severity or "MEDIUM"
            cvss_score = cve.cvss_v3.base_score
        elif cve.cvss_v2:
            cvss_score = cve.cvss_v2.base_score
            # Map CVSS v2 score to severity
            if cvss_score >= 7.0:
                severity = "HIGH"
            elif cvss_score >= 4.0:
                severity = "MEDIUM"
            else:
                severity = "LOW"
        
        return Vulnerability(
            id=cve.cve_id,
            source="NIST NVD",
            severity=severity,
            cvss_score=cvss_score,
            description=description,
            published=cve.published,
            updated=cve.last_modified
        )
    
    async def update_cve_database(self, days_back: int = 7):
        """Update local CVE database with recent vulnerabilities"""
        
        end_date = datetime.now(UTC)
        start_date = end_date - timedelta(days=days_back)
        
        logger.info(f"Updating CVE database for last {days_back} days...")
        
        async with NISTNVDClient(api_key=self.nvd_api_key) as nvd_client:
            cves = await nvd_client.search_cves(
                last_mod_start_date=start_date,
                last_mod_end_date=end_date,
                results_per_page=2000
            )
            
            self.db.store_cves(cves)
            logger.info(f"Updated database with {len(cves)} CVEs")
    
    def get_high_critical_cves(self) -> list[CVEItem]:
        """Get HIGH and CRITICAL severity CVEs from database"""
        
        return self.db.search_cves_by_severity(CVESeverity.HIGH)
    
    def generate_vulnerability_report(self, 
                                    scan_results: dict[str, list[Vulnerability]]) -> dict[str, Any]:
        """Generate comprehensive vulnerability report"""
        
        total_vulns = sum(len(vulns) for vulns in scan_results.values())
        
        severity_counts = {"CRITICAL": 0, "HIGH": 0, "MEDIUM": 0, "LOW": 0}
        critical_components = []
        
        for component_name, vulnerabilities in scan_results.items():
            component_severity = "LOW"
            
            for vuln in vulnerabilities:
                severity_counts[vuln.severity] += 1
                
                if vuln.severity in ["CRITICAL", "HIGH"]:
                    component_severity = vuln.severity
            
            if component_severity in ["CRITICAL", "HIGH"]:
                critical_components.append({
                    "component": component_name,
                    "severity": component_severity,
                    "vulnerability_count": len(vulnerabilities)
                })
        
        report = {
            "scan_timestamp": datetime.now(UTC).isoformat(),
            "total_components_scanned": len(scan_results),
            "total_vulnerabilities": total_vulns,
            "severity_breakdown": severity_counts,
            "critical_components": critical_components,
            "recommendations": self._generate_recommendations(scan_results)
        }
        
        return report
    
    def _generate_recommendations(self, 
                                scan_results: dict[str, list[Vulnerability]]) -> list[str]:
        """Generate security recommendations"""
        
        recommendations = []
        
        high_crit_components = []
        for component, vulns in scan_results.items():
            for vuln in vulns:
                if vuln.severity in ["CRITICAL", "HIGH"]:
                    high_crit_components.append(component)
                    break
        
        if high_crit_components:
            recommendations.append(
                f"URGENT: Update {len(high_crit_components)} components with HIGH/CRITICAL vulnerabilities"
            )
        
        recommendations.extend([
            "Enable automated dependency scanning in CI/CD pipeline",
            "Configure vulnerability alerts for new CVEs",
            "Implement regular security dependency updates",
            "Consider using tools like Dependabot or Renovate",
            "Establish security incident response procedures"
        ])
        
        return recommendations