#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/proofs/formal/solver_interface.py              |
# | ROLE: A4 - SMT Solver Interface for Formal Proofs        |
# | PLIK: core/proofs/formal/solver_interface.py              |
# | ROLA: A4 - Interfejs SMT Solver dla dowodów formalnych    |
# +-------------------------------------------------------------+

"""
PL: A4 Dowody formalne - interfejs dla solverów SMT (Z3/CVC5)
EN: A4 Formal Proofs - SMT solver interface (Z3/CVC5)

Enterprise-grade interface for SMT solvers providing formal proof generation
with artifact collection, deterministic execution, and fallback simulation.

Key Features:
- Z3 and CVC5 solver integration
- Proof artifact generation (DRAT/LFSC)
- Deterministic execution with seed control
- Simulation mode for testing without solvers
- Time and memory limits enforcement
- Counterexample generation for negative cases
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from datetime import UTC, datetime
from enum import Enum
import hashlib
import json
from pathlib import Path
from typing import Any

from core.logging import get_logger

logger = get_logger("formal_proofs")


class SolverType(Enum):
    """Supported SMT solver types"""
    Z3 = "z3"
    CVC5 = "cvc5"
    SIMULATE = "simulate"


class ProofResult(Enum):
    """Proof verification results"""
    SATISFIABLE = "sat"
    UNSATISFIABLE = "unsat"
    UNKNOWN = "unknown"
    TIMEOUT = "timeout"
    ERROR = "error"
    SIMULATED = "simulated"


@dataclass
class SolverConfig:
    """Configuration for SMT solver execution"""
    
    # Solver selection
    solver_type: SolverType = SolverType.Z3
    fallback_to_simulate: bool = True
    
    # Execution limits
    timeout_seconds: int = 300  # 5 minutes default
    memory_limit_mb: int = 8192  # 8GB default
    
    # Determinism
    random_seed: int = 42
    solver_version: str | None = None
    
    # Proof artifacts
    generate_artifacts: bool = True
    artifact_format: str = "drat"  # drat, lfsc, native
    save_counterexamples: bool = True
    
    # Advanced options
    solver_options: dict[str, Any] = field(default_factory=dict)
    debug_mode: bool = False


@dataclass 
class ProofArtifact:
    """Formal proof artifact with verification data"""
    
    # Metadata
    id: str
    timestamp: datetime
    solver_type: SolverType
    solver_version: str
    
    # Problem description
    smt_formula: str
    problem_hash: str
    
    # Results
    result: ProofResult
    execution_time_ms: int
    memory_used_mb: float
    
    # Proof artifacts
    proof_data: str | None = None  # DRAT/LFSC proof
    counterexample: dict[str, Any] | None = None
    witness: dict[str, Any] | None = None
    
    # Configuration
    config: SolverConfig = field(default_factory=SolverConfig)
    
    # Verification
    artifact_hash: str = ""
    verified: bool = False
    
    def __post_init__(self):
        """Generate artifact hash for integrity"""
        if not self.artifact_hash:
            content = f"{self.smt_formula}|{self.result.value}|{self.proof_data or ''}"
            self.artifact_hash = hashlib.sha256(content.encode()).hexdigest()
    
    def to_dict(self) -> dict[str, Any]:
        """Convert to dictionary for serialization"""
        return {
            "id": self.id,
            "timestamp": self.timestamp.isoformat(),
            "solver_type": self.solver_type.value,
            "solver_version": self.solver_version,
            "smt_formula": self.smt_formula,
            "problem_hash": self.problem_hash,
            "result": self.result.value,
            "execution_time_ms": self.execution_time_ms,
            "memory_used_mb": self.memory_used_mb,
            "proof_data": self.proof_data,
            "counterexample": self.counterexample,
            "witness": self.witness,
            "config": {
                "solver_type": self.config.solver_type.value,
                "timeout_seconds": self.config.timeout_seconds,
                "memory_limit_mb": self.config.memory_limit_mb,
                "random_seed": self.config.random_seed,
                "artifact_format": self.config.artifact_format
            },
            "artifact_hash": self.artifact_hash,
            "verified": self.verified
        }
    
    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "ProofArtifact":
        """Create from dictionary"""
        config = SolverConfig(
            solver_type=SolverType(data["config"]["solver_type"]),
            timeout_seconds=data["config"]["timeout_seconds"],
            memory_limit_mb=data["config"]["memory_limit_mb"],
            random_seed=data["config"]["random_seed"],
            artifact_format=data["config"]["artifact_format"]
        )
        
        return cls(
            id=data["id"],
            timestamp=datetime.fromisoformat(data["timestamp"]),
            solver_type=SolverType(data["solver_type"]),
            solver_version=data["solver_version"],
            smt_formula=data["smt_formula"],
            problem_hash=data["problem_hash"],
            result=ProofResult(data["result"]),
            execution_time_ms=data["execution_time_ms"],
            memory_used_mb=data["memory_used_mb"],
            proof_data=data.get("proof_data"),
            counterexample=data.get("counterexample"),
            witness=data.get("witness"),
            config=config,
            artifact_hash=data["artifact_hash"],
            verified=data["verified"]
        )


class SMTSolverInterface(ABC):
    """Abstract interface for SMT solvers"""
    
    def __init__(self, config: SolverConfig):
        self.config = config
        self.logger = get_logger(f"smt_solver_{config.solver_type.value}")
    
    @abstractmethod
    async def solve(self, smt_formula: str, 
                   problem_id: str | None = None) -> ProofArtifact:
        """
        Solve SMT formula and generate proof artifact
        
        Args:
            smt_formula: SMT-LIB format formula
            problem_id: Optional identifier for the problem
            
        Returns:
            ProofArtifact with results and proof data
        """
        pass
    
    @abstractmethod
    async def verify_proof(self, artifact: ProofArtifact) -> bool:
        """
        Verify proof artifact independently
        
        Args:
            artifact: Proof artifact to verify
            
        Returns:
            True if proof is valid
        """
        pass
    
    @abstractmethod
    def is_available(self) -> bool:
        """Check if solver is available and functional"""
        pass
    
    @abstractmethod
    def get_version(self) -> str:
        """Get solver version information"""
        pass
    
    def generate_problem_hash(self, smt_formula: str) -> str:
        """Generate deterministic hash for SMT problem"""
        normalized = smt_formula.strip().replace('\r\n', '\n')
        return hashlib.sha256(normalized.encode()).hexdigest()
    
    def create_artifact_id(self, problem_hash: str) -> str:
        """Create unique artifact ID"""
        timestamp = datetime.now(UTC).strftime("%Y%m%d_%H%M%S")
        solver_id = self.config.solver_type.value
        return f"{solver_id}_{timestamp}_{problem_hash[:8]}"


class ProofArtifactManager:
    """Manager for storing and retrieving proof artifacts"""
    
    def __init__(self, storage_path: Path):
        self.storage_path = Path(storage_path)
        self.storage_path.mkdir(parents=True, exist_ok=True)
        self.logger = get_logger("proof_artifact_manager")
    
    async def store_artifact(self, artifact: ProofArtifact) -> Path:
        """Store proof artifact to filesystem"""
        
        artifact_file = self.storage_path / f"{artifact.id}.json"
        
        try:
            with open(artifact_file, 'w', encoding='utf-8') as f:
                json.dump(artifact.to_dict(), f, indent=2, ensure_ascii=False)
            
            # Store proof data separately if large
            if artifact.proof_data and len(artifact.proof_data) > 10000:
                proof_file = self.storage_path / f"{artifact.id}_proof.txt"
                with open(proof_file, 'w', encoding='utf-8') as f:
                    f.write(artifact.proof_data)
                
                # Update artifact to reference external file
                artifact_data = artifact.to_dict()
                artifact_data["proof_data"] = f"{artifact.id}_proof.txt"
                
                with open(artifact_file, 'w', encoding='utf-8') as f:
                    json.dump(artifact_data, f, indent=2, ensure_ascii=False)
            
            self.logger.info(f"Stored proof artifact: {artifact.id}")
            return artifact_file
            
        except Exception as e:
            self.logger.error(f"Failed to store artifact {artifact.id}: {e}")
            raise
    
    async def load_artifact(self, artifact_id: str) -> ProofArtifact | None:
        """Load proof artifact from filesystem"""
        
        artifact_file = self.storage_path / f"{artifact_id}.json"
        
        if not artifact_file.exists():
            return None
        
        try:
            with open(artifact_file, encoding='utf-8') as f:
                data = json.load(f)
            
            # Load external proof data if referenced
            if (isinstance(data.get("proof_data"), str) and 
                data["proof_data"].endswith("_proof.txt")):
                proof_file = self.storage_path / data["proof_data"]
                if proof_file.exists():
                    with open(proof_file, encoding='utf-8') as f:
                        data["proof_data"] = f.read()
            
            return ProofArtifact.from_dict(data)
            
        except Exception as e:
            self.logger.error(f"Failed to load artifact {artifact_id}: {e}")
            return None
    
    async def list_artifacts(self, 
                           solver_type: SolverType | None = None,
                           since: datetime | None = None) -> list[str]:
        """List available proof artifacts"""
        
        artifacts = []
        
        for artifact_file in self.storage_path.glob("*.json"):
            if artifact_file.name.endswith("_proof.txt"):
                continue
                
            artifact_id = artifact_file.stem
            
            # Filter by solver type if specified
            if solver_type:
                solver_prefix = solver_type.value
                if not artifact_id.startswith(solver_prefix):
                    continue
            
            # Filter by date if specified  
            if since:
                try:
                    # Extract timestamp from artifact ID
                    parts = artifact_id.split('_')
                    if len(parts) >= 3:
                        timestamp_str = f"{parts[1]}_{parts[2]}"
                        artifact_time = datetime.strptime(timestamp_str, "%Y%m%d_%H%M%S")
                        if artifact_time < since:
                            continue
                except:
                    pass  # Skip if can't parse timestamp
            
            artifacts.append(artifact_id)
        
        return sorted(artifacts)


# Export public interface
__all__ = [
    'SolverType',
    'ProofResult', 
    'SolverConfig',
    'ProofArtifact',
    'SMTSolverInterface',
    'ProofArtifactManager'
]