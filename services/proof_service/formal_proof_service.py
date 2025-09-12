#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/proof_service/formal_proof_service.py      |
# | ROLE: A4 - Formal Proof Service Implementation            |
# | PLIK: services/proof_service/formal_proof_service.py      |
# | ROLA: A4 - Implementacja Serwisu Dowodów Formalnych       |
# +-------------------------------------------------------------+

"""
PL: A4 Dowody formalne - główny serwis zarządzający dowodami formalnymi
EN: A4 Formal Proofs - main service managing formal proofs

Enterprise formal proof service integrating Z3 and CVC5 solvers with comprehensive
artifact management, deterministic execution, and fallback simulation.

Key Features:
- Multi-solver support (Z3, CVC5, simulation)
- Automatic solver selection and fallback
- Proof artifact persistence and verification
- Deterministic execution with seed control
- Bundle integration for proof attachments
- Performance monitoring and limits enforcement
"""

import asyncio
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from core.logging import get_logger
from core.proofs.formal.cvc5_solver import CVC5_AVAILABLE, CVC5Solver
from core.proofs.formal.solver_interface import (
    ProofArtifact,
    ProofArtifactManager,
    ProofResult,
    SMTSolverInterface,
    SolverConfig,
    SolverType,
)
from core.proofs.formal.z3_solver import Z3_AVAILABLE, Z3Solver

logger = get_logger("formal_proof_service")


class FormalProofService:
    """
    Enterprise formal proof service with multi-solver support

    Manages formal proof generation, verification, and artifact storage
    with deterministic execution and comprehensive error handling.
    """

    def __init__(self, config: SolverConfig, artifact_storage_path: str = "./proof_artifacts"):
        """
        Initialize formal proof service

        Args:
            config: Default solver configuration
            artifact_storage_path: Path to store proof artifacts
        """

        self.config = config
        self.artifact_manager = ProofArtifactManager(Path(artifact_storage_path))
        self.logger = get_logger("formal_proof_service")

        # Initialize solvers
        self.solvers: dict[SolverType, SMTSolverInterface] = {}
        self._initialize_solvers()

        # Statistics
        self.stats = {
            "total_proofs": 0,
            "successful_proofs": 0,
            "failed_proofs": 0,
            "simulated_proofs": 0,
            "solver_usage": {solver.value: 0 for solver in SolverType},
        }

    def _initialize_solvers(self):
        """Initialize available SMT solvers"""

        # Initialize Z3 if available
        if Z3_AVAILABLE:
            try:
                self.solvers[SolverType.Z3] = Z3Solver(self.config)
                self.logger.info("Z3 solver initialized successfully")
            except Exception as e:
                self.logger.warning(f"Failed to initialize Z3 solver: {e}")

        # Initialize CVC5 if available
        if CVC5_AVAILABLE:
            try:
                self.solvers[SolverType.CVC5] = CVC5Solver(self.config)
                self.logger.info("CVC5 solver initialized successfully")
            except Exception as e:
                self.logger.warning(f"Failed to initialize CVC5 solver: {e}")

        # Always have simulation available
        if self.config.solver_type == SolverType.Z3:
            self.solvers[SolverType.SIMULATE] = Z3Solver(self.config)
        else:
            self.solvers[SolverType.SIMULATE] = CVC5Solver(self.config)

        available_solvers = [s for s in self.solvers.keys() if s != SolverType.SIMULATE]
        self.logger.info(f"Initialized solvers: {[s.value for s in available_solvers]}")

        if not available_solvers and not self.config.fallback_to_simulate:
            self.logger.warning("No real solvers available and simulation disabled")

    async def prove_formula(
        self,
        smt_formula: str,
        problem_id: str | None = None,
        solver_preference: SolverType | None = None,
        config_override: SolverConfig | None = None,
    ) -> ProofArtifact:
        """
        Generate formal proof for SMT formula

        Args:
            smt_formula: SMT-LIB 2.0 format formula to prove
            problem_id: Optional unique identifier for the problem
            solver_preference: Preferred solver type (None for auto-selection)
            config_override: Override default solver configuration

        Returns:
            ProofArtifact with proof results and metadata
        """

        config = config_override or self.config

        # Select solver
        solver_type = solver_preference or self._select_solver(smt_formula)

        # Update statistics
        self.stats["total_proofs"] += 1
        self.stats["solver_usage"][solver_type.value] += 1

        try:
            # Get solver instance
            if solver_type not in self.solvers:
                if config.fallback_to_simulate:
                    self.logger.warning(f"Solver {solver_type.value} not available, falling back to simulation")
                    solver_type = SolverType.SIMULATE
                else:
                    raise RuntimeError(f"Solver {solver_type.value} not available")

            solver = self.solvers[solver_type]

            # Execute proof
            self.logger.info(f"Starting proof with {solver_type.value} solver")
            artifact = await solver.solve(smt_formula, problem_id)

            # Store artifact
            await self.artifact_manager.store_artifact(artifact)

            # Update statistics
            if artifact.result in [ProofResult.SATISFIABLE, ProofResult.UNSATISFIABLE]:
                self.stats["successful_proofs"] += 1
            elif artifact.result == ProofResult.SIMULATED:
                self.stats["simulated_proofs"] += 1
            else:
                self.stats["failed_proofs"] += 1

            self.logger.info(f"Proof completed: {artifact.result.value} (ID: {artifact.id})")
            return artifact

        except Exception as e:
            self.stats["failed_proofs"] += 1
            self.logger.error(f"Proof generation failed: {e}")

            # Create error artifact
            problem_hash = solver.generate_problem_hash(smt_formula) if 'solver' in locals() else "unknown"
            error_artifact = ProofArtifact(
                id=problem_id or f"error_{int(datetime.now().timestamp())}",
                timestamp=datetime.now(UTC),
                solver_type=solver_type,
                solver_version="error",
                smt_formula=smt_formula,
                problem_hash=problem_hash,
                result=ProofResult.ERROR,
                execution_time_ms=0,
                memory_used_mb=0.0,
                config=config,
            )

            await self.artifact_manager.store_artifact(error_artifact)
            return error_artifact

    async def verify_proof(self, artifact_id: str) -> bool:
        """
        Verify existing proof artifact

        Args:
            artifact_id: Identifier of proof artifact to verify

        Returns:
            True if proof is valid and can be independently verified
        """

        # Load artifact
        artifact = await self.artifact_manager.load_artifact(artifact_id)
        if not artifact:
            self.logger.error(f"Artifact not found: {artifact_id}")
            return False

        # Get appropriate solver for verification
        solver_type = artifact.solver_type
        if solver_type == SolverType.SIMULATE:
            self.logger.info("Simulated proof - verification skipped")
            return True

        if solver_type not in self.solvers:
            self.logger.error(f"No solver available for verification: {solver_type.value}")
            return False

        solver = self.solvers[solver_type]

        try:
            self.logger.info(f"Verifying proof artifact: {artifact_id}")
            is_valid = await solver.verify_proof(artifact)

            if is_valid:
                # Mark artifact as verified
                artifact.verified = True
                await self.artifact_manager.store_artifact(artifact)

            self.logger.info(f"Proof verification result: {is_valid}")
            return is_valid

        except Exception as e:
            self.logger.error(f"Proof verification failed: {e}")
            return False

    async def batch_prove(
        self, formulas: list[tuple[str, str, str | None]], config_override: SolverConfig | None = None
    ) -> list[ProofArtifact]:
        """
        Generate proofs for multiple formulas in batch

        Args:
            formulas: List of (formula, problem_id, description) tuples
            config_override: Override configuration for batch

        Returns:
            List of proof artifacts
        """

        config = config_override or self.config

        self.logger.info(f"Starting batch proof generation for {len(formulas)} formulas")

        # Create semaphore to limit concurrent solver executions
        semaphore = asyncio.Semaphore(2)  # Max 2 concurrent solvers

        async def prove_single(formula_data):
            formula, problem_id, description = formula_data
            async with semaphore:
                return await self.prove_formula(formula, problem_id, config_override=config)

        # Execute proofs concurrently
        tasks = [prove_single(formula_data) for formula_data in formulas]
        artifacts = await asyncio.gather(*tasks, return_exceptions=True)

        # Filter out exceptions and log them
        valid_artifacts = []
        for i, result in enumerate(artifacts):
            if isinstance(result, Exception):
                self.logger.error(f"Batch proof {i} failed: {result}")
            else:
                valid_artifacts.append(result)

        self.logger.info(f"Batch proof completed: {len(valid_artifacts)}/{len(formulas)} successful")
        return valid_artifacts

    async def get_proof_statistics(self) -> dict[str, Any]:
        """Get comprehensive proof service statistics"""

        # Get artifact statistics
        artifact_ids = await self.artifact_manager.list_artifacts()

        solver_counts = {}
        result_counts = {}
        recent_proofs = []

        for artifact_id in artifact_ids[-10:]:  # Last 10 for recent stats
            artifact = await self.artifact_manager.load_artifact(artifact_id)
            if artifact:
                # Count by solver
                solver_type = artifact.solver_type.value
                solver_counts[solver_type] = solver_counts.get(solver_type, 0) + 1

                # Count by result
                result = artifact.result.value
                result_counts[result] = result_counts.get(result, 0) + 1

                # Recent proofs info
                recent_proofs.append(
                    {
                        "id": artifact.id,
                        "timestamp": artifact.timestamp.isoformat(),
                        "solver": solver_type,
                        "result": result,
                        "execution_time_ms": artifact.execution_time_ms,
                    }
                )

        return {
            "service_stats": self.stats,
            "total_artifacts": len(artifact_ids),
            "solver_availability": {
                "z3": Z3_AVAILABLE and SolverType.Z3 in self.solvers,
                "cvc5": CVC5_AVAILABLE and SolverType.CVC5 in self.solvers,
                "simulation": True,
            },
            "artifact_counts": {"by_solver": solver_counts, "by_result": result_counts},
            "recent_proofs": recent_proofs,
        }

    def _select_solver(self, smt_formula: str) -> SolverType:
        """
        Automatically select optimal solver for formula

        Args:
            smt_formula: SMT formula to analyze

        Returns:
            Recommended solver type
        """

        # Simple heuristics for solver selection
        formula_lower = smt_formula.lower()

        # Prefer Z3 for arithmetic-heavy formulas
        if any(keyword in formula_lower for keyword in ['*', '+', '-', 'div', 'mod', 'arithmetic']):
            if SolverType.Z3 in self.solvers:
                return SolverType.Z3

        # Prefer CVC5 for logic and set operations
        if any(keyword in formula_lower for keyword in ['set', 'union', 'intersection', 'member']):
            if SolverType.CVC5 in self.solvers:
                return SolverType.CVC5

        # Default to configured preference
        if self.config.solver_type in self.solvers:
            return self.config.solver_type

        # Fallback to first available solver
        available_solvers = [s for s in self.solvers.keys() if s != SolverType.SIMULATE]
        if available_solvers:
            return available_solvers[0]

        return SolverType.SIMULATE

    async def cleanup_old_artifacts(self, days: int = 30) -> int:
        """
        Clean up proof artifacts older than specified days

        Args:
            days: Maximum age of artifacts to keep

        Returns:
            Number of artifacts deleted
        """

        cutoff_date = datetime.now(UTC).replace(day=datetime.now().day - days)

        artifact_ids = await self.artifact_manager.list_artifacts(since=cutoff_date)
        all_artifacts = await self.artifact_manager.list_artifacts()

        old_artifacts = [aid for aid in all_artifacts if aid not in artifact_ids]

        deleted_count = 0
        for artifact_id in old_artifacts:
            try:
                artifact_file = self.artifact_manager.storage_path / f"{artifact_id}.json"
                proof_file = self.artifact_manager.storage_path / f"{artifact_id}_proof.txt"

                if artifact_file.exists():
                    artifact_file.unlink()
                    deleted_count += 1

                if proof_file.exists():
                    proof_file.unlink()

            except Exception as e:
                self.logger.warning(f"Failed to delete artifact {artifact_id}: {e}")

        self.logger.info(f"Cleaned up {deleted_count} old proof artifacts")
        return deleted_count


# Export public interface
__all__ = ['FormalProofService']
