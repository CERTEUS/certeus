#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pco/evidence_graph.py                           |
# | ROLE: Evidence Graph generator (PROV JSON-LD)             |
# | PLIK: core/pco/evidence_graph.py                           |
# | ROLA: Generator Evidence Graph (PROV JSON-LD)             |
# +-------------------------------------------------------------+

"""
PL: Generator Evidence Graph w formacie PROV JSON-LD z eksportem RO-Crate.
EN: Evidence Graph generator in PROV JSON-LD format with RO-Crate export.
"""

from __future__ import annotations

from datetime import datetime
import hashlib
import json
from pathlib import Path
from typing import Any
import uuid


class EvidenceNode:
    """Węzeł w Evidence Graph."""

    def __init__(
        self,
        id: str,
        type: str,
        label: str | None = None,
        attributes: dict[str, Any] | None = None,
        pii_level: str = "public",
    ):
        self.id = id
        self.type = type  # Entity, Activity, Agent
        self.label = label or id
        self.attributes = attributes or {}
        self.pii_level = pii_level  # public, restricted, confidential

    def to_prov(self) -> dict[str, Any]:
        """Konwertuje do formatu PROV JSON-LD."""
        node = {"prov:id": self.id, "prov:type": self.type, "prov:label": self.label}

        # Dodaj atrybuty z prefiksami PROV
        for key, value in self.attributes.items():
            if not key.startswith("prov:"):
                key = f"certeus:{key}"
            node[key] = value

        return node

    def is_public(self) -> bool:
        """Sprawdza czy węzeł może być publiczny."""
        return self.pii_level == "public"


class EvidenceEdge:
    """Krawędź w Evidence Graph."""

    def __init__(
        self,
        id: str,
        relation_type: str,
        source_id: str,
        target_id: str,
        label: str | None = None,
        attributes: dict[str, Any] | None = None,
    ):
        self.id = id
        self.relation_type = relation_type  # wasGeneratedBy, used, wasAssociatedWith, etc.
        self.source_id = source_id
        self.target_id = target_id
        self.label = label
        self.attributes = attributes or {}

    def to_prov(self) -> dict[str, Any]:
        """Konwertuje do formatu PROV JSON-LD."""
        edge = {"prov:id": self.id, "prov:type": self.relation_type}

        # Mapowanie typów relacji na odpowiednie pola PROV
        if self.relation_type == "wasGeneratedBy":
            edge["prov:entity"] = self.source_id
            edge["prov:activity"] = self.target_id
        elif self.relation_type == "used":
            edge["prov:activity"] = self.source_id
            edge["prov:entity"] = self.target_id
        elif self.relation_type == "wasAssociatedWith":
            edge["prov:activity"] = self.source_id
            edge["prov:agent"] = self.target_id
        else:
            edge["prov:source"] = self.source_id
            edge["prov:target"] = self.target_id

        if self.label:
            edge["prov:label"] = self.label

        for key, value in self.attributes.items():
            if not key.startswith("prov:"):
                key = f"certeus:{key}"
            edge[key] = value

        return edge


class EvidenceGraph:
    """Evidence Graph w formacie PROV JSON-LD."""

    def __init__(self, case_id: str):
        self.case_id = case_id
        self.nodes: dict[str, EvidenceNode] = {}
        self.edges: dict[str, EvidenceEdge] = {}
        self.created_at = datetime.utcnow()

    def add_entity(
        self, id: str, label: str | None = None, attributes: dict[str, Any] | None = None, pii_level: str = "public"
    ) -> EvidenceNode:
        """Dodaje entność do grafu."""
        node = EvidenceNode(id, "prov:Entity", label, attributes, pii_level)
        self.nodes[id] = node
        return node

    def add_activity(
        self,
        id: str,
        label: str | None = None,
        start_time: datetime | None = None,
        end_time: datetime | None = None,
        attributes: dict[str, Any] | None = None,
        pii_level: str = "public",
    ) -> EvidenceNode:
        """Dodaje aktywność do grafu."""
        attrs = attributes or {}
        if start_time:
            attrs["prov:startTime"] = start_time.isoformat()
        if end_time:
            attrs["prov:endTime"] = end_time.isoformat()

        node = EvidenceNode(id, "prov:Activity", label, attrs, pii_level)
        self.nodes[id] = node
        return node

    def add_agent(
        self,
        id: str,
        label: str | None = None,
        agent_type: str = "SoftwareAgent",
        attributes: dict[str, Any] | None = None,
        pii_level: str = "restricted",
    ) -> EvidenceNode:
        """Dodaje agenta do grafu."""
        attrs = attributes or {}
        attrs["prov:type"] = f"prov:{agent_type}"

        node = EvidenceNode(id, "prov:Agent", label, attrs, pii_level)
        self.nodes[id] = node
        return node

    def add_generation(
        self, entity_id: str, activity_id: str, time: datetime | None = None, attributes: dict[str, Any] | None = None
    ) -> EvidenceEdge:
        """Dodaje relację wasGeneratedBy."""
        edge_id = f"gen_{uuid.uuid4().hex[:8]}"
        attrs = attributes or {}
        if time:
            attrs["prov:time"] = time.isoformat()

        edge = EvidenceEdge(edge_id, "wasGeneratedBy", entity_id, activity_id, attributes=attrs)
        self.edges[edge_id] = edge
        return edge

    def add_usage(
        self, activity_id: str, entity_id: str, time: datetime | None = None, attributes: dict[str, Any] | None = None
    ) -> EvidenceEdge:
        """Dodaje relację used."""
        edge_id = f"use_{uuid.uuid4().hex[:8]}"
        attrs = attributes or {}
        if time:
            attrs["prov:time"] = time.isoformat()

        edge = EvidenceEdge(edge_id, "used", activity_id, entity_id, attributes=attrs)
        self.edges[edge_id] = edge
        return edge

    def add_association(
        self, activity_id: str, agent_id: str, plan_id: str | None = None, attributes: dict[str, Any] | None = None
    ) -> EvidenceEdge:
        """Dodaje relację wasAssociatedWith."""
        edge_id = f"assoc_{uuid.uuid4().hex[:8]}"
        attrs = attributes or {}
        if plan_id:
            attrs["prov:plan"] = plan_id

        edge = EvidenceEdge(edge_id, "wasAssociatedWith", activity_id, agent_id, attributes=attrs)
        self.edges[edge_id] = edge
        return edge

    def add_derivation(
        self,
        derived_entity_id: str,
        source_entity_id: str,
        activity_id: str | None = None,
        attributes: dict[str, Any] | None = None,
    ) -> EvidenceEdge:
        """Dodaje relację wasDerivedFrom."""
        edge_id = f"der_{uuid.uuid4().hex[:8]}"
        attrs = attributes or {}
        if activity_id:
            attrs["prov:activity"] = activity_id

        edge = EvidenceEdge(edge_id, "wasDerivedFrom", derived_entity_id, source_entity_id, attributes=attrs)
        self.edges[edge_id] = edge
        return edge

    def to_prov_json_ld(self, include_private: bool = True) -> dict[str, Any]:
        """Eksportuje graf do formatu PROV JSON-LD."""
        context = {
            "@context": {
                "prov": "http://www.w3.org/ns/prov#",
                "certeus": "https://certeus.dev/ns/evidence#",
                "xsd": "http://www.w3.org/2001/XMLSchema#",
                "foaf": "http://xmlns.com/foaf/0.1/",
                "dcterms": "http://purl.org/dc/terms/",
            }
        }

        graph_data = []

        # Dodaj węzły
        for node in self.nodes.values():
            if include_private or node.is_public():
                graph_data.append(node.to_prov())

        # Dodaj krawędzie
        for edge in self.edges.values():
            # Sprawdź czy oba końce krawędzi są dostępne
            source_node = self.nodes.get(edge.source_id)
            target_node = self.nodes.get(edge.target_id)

            if include_private or (source_node and source_node.is_public() and target_node and target_node.is_public()):
                graph_data.append(edge.to_prov())

        return {
            **context,
            "@graph": graph_data,
            "certeus:case_id": self.case_id,
            "certeus:created_at": self.created_at.isoformat(),
            "certeus:graph_stats": {
                "node_count": len([n for n in self.nodes.values() if include_private or n.is_public()]),
                "edge_count": len(self.edges),
                "public_node_count": len([n for n in self.nodes.values() if n.is_public()]),
            },
        }

    def to_public_summary(self) -> dict[str, Any]:
        """Tworzy publiczne streszczenie grafu."""
        public_nodes = [n for n in self.nodes.values() if n.is_public()]

        return {
            "node_count": len(self.nodes),
            "edge_count": len(self.edges),
            "public_node_count": len(public_nodes),
            "public_nodes": [
                {
                    "id": node.id,
                    "type": node.type,
                    "label": node.label,
                    "public_attributes": {
                        k: v
                        for k, v in node.attributes.items()
                        if not k.startswith("pii_") and not k.startswith("private_")
                    },
                }
                for node in public_nodes[:10]  # Limit to first 10 nodes
            ],
        }


class EvidenceGraphBuilder:
    """Builder dla Evidence Graph z automatycznym tworzeniem na podstawie PCO."""

    @staticmethod
    def from_pco_bundle(pco_data: dict[str, Any]) -> EvidenceGraph:
        """Tworzy Evidence Graph na podstawie PCO Bundle."""
        case_id = pco_data.get("case_id", "unknown")
        graph = EvidenceGraph(case_id)

        # Dodaj podstawowe entności
        # PCO jako główna entność
        graph.add_entity(
            f"pco:{case_id}",
            f"PCO Bundle {case_id}",
            {
                "prov:type": "certeus:PCOBundle",
                "certeus:version": pco_data.get("version", "1.0"),
                "certeus:status": pco_data.get("status", "PENDING"),
            },
        )

        # Dodaj źródła jako entności
        sources = pco_data.get("sources", [])
        for source in sources:
            graph.add_entity(
                f"source:{source['id']}",
                f"Source {source['id']}",
                {
                    "prov:type": "certeus:LegalSource",
                    "certeus:uri": source["uri"],
                    "certeus:digest": source["digest"],
                    "certeus:license": source.get("license", "unknown"),
                },
            )

            # PCO używa tego źródła
            graph.add_usage(f"pco:{case_id}", f"source:{source['id']}")

        # Dodaj derivations jako aktywności
        derivations = pco_data.get("derivations", [])
        for i, derivation in enumerate(derivations):
            activity_id = f"proof_activity_{i}"
            graph.add_activity(
                activity_id,
                f"Proof generation with {derivation['solver']}",
                attributes={
                    "prov:type": "certeus:ProofGeneration",
                    "certeus:solver": derivation["solver"],
                    "certeus:proof_format": derivation["proof_format"],
                    "certeus:artifact_digest": derivation["artifact_digest"],
                },
            )

            # Proof entity
            graph.add_entity(
                f"proof:{derivation['claim_id']}",
                f"Proof for {derivation['claim_id']}",
                {"prov:type": "certeus:FormalProof", "certeus:format": derivation["proof_format"]},
            )

            # Proof został wygenerowany przez aktywność
            graph.add_generation(f"proof:{derivation['claim_id']}", activity_id)

            # Solver jako agent
            graph.add_agent(
                f"solver:{derivation['solver']}",
                f"Solver {derivation['solver']}",
                attributes={
                    "certeus:version": derivation.get("solver_version", "unknown"),
                    "certeus:type": "TheoremProver",
                },
            )

            # Aktywność była powiązana z solverem
            graph.add_association(activity_id, f"solver:{derivation['solver']}")

        # Dodaj claims jako entności
        claims = pco_data.get("claims", [])
        for claim in claims:
            # Redakcja PII w claims - tylko publiczne streszczenie
            pii_level = "restricted" if len(claim.get("text", "")) > 100 else "public"

            graph.add_entity(
                f"claim:{claim['id']}",
                f"Claim {claim['id']}",
                {
                    "prov:type": "certeus:LegalClaim",
                    "certeus:confidence": claim.get("confidence", 0.0),
                    "certeus:text_length": len(claim.get("text", "")),
                    "certeus:legal_domain": claim.get("legal_basis", {}).get("domain", "unknown"),
                },
                pii_level=pii_level,
            )

            # PCO zawiera ten claim
            graph.add_derivation(f"pco:{case_id}", f"claim:{claim['id']}")

        # Podpisy jako aktywności
        signatures = pco_data.get("signatures", [])
        for i, signature in enumerate(signatures):
            graph.add_activity(
                f"sign_activity_{i}",
                f"Digital signature by {signature['role']}",
                attributes={
                    "prov:type": "certeus:DigitalSigning",
                    "certeus:algorithm": signature["alg"],
                    "certeus:role": signature["role"],
                    "certeus:key_id": signature["key_id"],
                },
            )

            # Signing agent (anonimizowany)
            agent_id = f"signer:{signature['key_id'][:8]}"
            graph.add_agent(
                agent_id,
                f"Signer ({signature['role']})",
                attributes={"certeus:role": signature["role"], "certeus:algorithm": signature["alg"]},
                pii_level="restricted",
            )

            graph.add_association(f"sign_activity_{i}", agent_id)

            # Podpisana wersja PCO
            graph.add_entity(
                f"signed_pco_{i}",
                f"PCO signed by {signature['role']}",
                {"prov:type": "certeus:SignedPCO", "certeus:signature_algorithm": signature["alg"]},
            )

            graph.add_generation(f"signed_pco_{i}", f"sign_activity_{i}")
            graph.add_usage(f"sign_activity_{i}", f"pco:{case_id}")

        return graph


class ROCrateExporter:
    """Eksporter Evidence Graph do formatu RO-Crate."""

    @staticmethod
    def export_evidence_graph(graph: EvidenceGraph, output_dir: Path, include_private: bool = False) -> Path:
        """Eksportuje Evidence Graph do RO-Crate."""
        output_dir = Path(output_dir)
        output_dir.mkdir(exist_ok=True)

        # Główny plik ro-crate-metadata.json
        metadata = {
            "@context": [
                "https://w3id.org/ro/crate/1.1/context",
                {"certeus": "https://certeus.dev/ns/evidence#", "prov": "http://www.w3.org/ns/prov#"},
            ],
            "@graph": [
                {
                    "@type": "CreativeWork",
                    "@id": "ro-crate-metadata.json",
                    "conformsTo": {"@id": "https://w3id.org/ro/crate/1.1"},
                    "about": {"@id": "./"},
                    "description": f"Evidence Graph for case {graph.case_id}",
                },
                {
                    "@type": ["Dataset", "certeus:EvidenceGraph"],
                    "@id": "./",
                    "name": f"Evidence Graph - {graph.case_id}",
                    "description": f"PROV-compliant evidence graph for legal case {graph.case_id}",
                    "dateCreated": graph.created_at.isoformat(),
                    "hasPart": [{"@id": "evidence_graph.json"}, {"@id": "public_summary.json"}],
                    "conformsTo": [
                        {"@id": "https://w3.org/TR/prov-json/"},
                        {"@id": "https://certeus.dev/schemas/evidence-graph/v1.0"},
                    ],
                },
            ],
        }

        # Zapisz metadane RO-Crate
        with open(output_dir / "ro-crate-metadata.json", 'w', encoding='utf-8') as f:
            json.dump(metadata, f, indent=2, ensure_ascii=False)

        # Zapisz pełny Evidence Graph
        evidence_data = graph.to_prov_json_ld(include_private=include_private)
        with open(output_dir / "evidence_graph.json", 'w', encoding='utf-8') as f:
            json.dump(evidence_data, f, indent=2, ensure_ascii=False)

        # Zapisz publiczne streszczenie
        public_summary = graph.to_public_summary()
        with open(output_dir / "public_summary.json", 'w', encoding='utf-8') as f:
            json.dump(public_summary, f, indent=2, ensure_ascii=False)

        # Generuj manifest
        manifest = {
            "case_id": graph.case_id,
            "created_at": graph.created_at.isoformat(),
            "files": [
                {
                    "name": "ro-crate-metadata.json",
                    "type": "metadata",
                    "size": (output_dir / "ro-crate-metadata.json").stat().st_size,
                },
                {
                    "name": "evidence_graph.json",
                    "type": "evidence_graph",
                    "format": "prov-json-ld",
                    "size": (output_dir / "evidence_graph.json").stat().st_size,
                },
                {
                    "name": "public_summary.json",
                    "type": "public_summary",
                    "size": (output_dir / "public_summary.json").stat().st_size,
                },
            ],
            "checksum": {"algorithm": "sha256", "value": ROCrateExporter._calculate_directory_hash(output_dir)},
        }

        with open(output_dir / "manifest.json", 'w', encoding='utf-8') as f:
            json.dump(manifest, f, indent=2, ensure_ascii=False)

        return output_dir

    @staticmethod
    def _calculate_directory_hash(directory: Path) -> str:
        """Oblicza hash SHA256 dla całego katalogu."""
        hasher = hashlib.sha256()
        for file_path in sorted(directory.glob("*.json")):
            hasher.update(file_path.name.encode('utf-8'))
            hasher.update(file_path.read_bytes())
        return hasher.hexdigest()


# CLI interface
if __name__ == "__main__":
    import argparse
    import sys

    parser = argparse.ArgumentParser(description="Evidence Graph Generator")
    parser.add_argument("pco_file", help="Path to PCO JSON file")
    parser.add_argument("--output", "-o", help="Output directory for RO-Crate", default="./evidence_output")
    parser.add_argument("--include-private", action="store_true", help="Include private data")
    parser.add_argument("--format", choices=["prov", "rocrate", "both"], default="both", help="Output format")

    args = parser.parse_args()

    try:
        with open(args.pco_file, encoding='utf-8') as f:
            pco_data = json.load(f)

        graph = EvidenceGraphBuilder.from_pco_bundle(pco_data)
        output_dir = Path(args.output)

        if args.format in ["prov", "both"]:
            prov_data = graph.to_prov_json_ld(include_private=args.include_private)
            output_dir.mkdir(exist_ok=True)
            with open(output_dir / "evidence_graph.json", 'w', encoding='utf-8') as f:
                json.dump(prov_data, f, indent=2, ensure_ascii=False)
            print(f"✓ PROV JSON-LD saved to {output_dir / 'evidence_graph.json'}")

        if args.format in ["rocrate", "both"]:
            crate_dir = ROCrateExporter.export_evidence_graph(
                graph, output_dir / "ro-crate", include_private=args.include_private
            )
            print(f"✓ RO-Crate exported to {crate_dir}")

    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)
