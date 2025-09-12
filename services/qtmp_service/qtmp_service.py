# CERTEUS Engine - A5 QTMP Service
# Quantum-Resistance Temporal & Metrology Protocol
# Service: Measurement processing, verification, and storage

import asyncio
import json
import logging
import uuid
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Union

from core.qtmp.measurements.measurement_model import (
    MeasurementMetadata, MeasurementResult, create_simple_measurement)
from core.qtmp.uncertainty.uncertainty_budget import (UncertaintyBudget,
                                                      UncertaintyComponent,
                                                      UncertaintyType)
from core.qtmp.units.unit_registry import unit_registry
from services.ledger_service.postgres_ledger import PostgreSQLLedger

logger = logging.getLogger(__name__)

class QTMPService:
    """
    Enterprise QTMP service for measurement processing and verification
    
    Features:
    - Measurement creation and validation
    - Uncertainty analysis and propagation
    - Unit conversion and compatibility checking
    - Integration with A2 Ledger for persistence
    - Measurement verification and traceability
    - Batch processing capabilities
    """
    
    def __init__(self, ledger_service: Optional[PostgreSQLLedger] = None):
        self.ledger_service = ledger_service
        self._measurements_cache: Dict[str, MeasurementResult] = {}
    
    async def create_measurement(
        self,
        value: float,
        unit: str,
        uncertainty_components: List[Dict[str, Any]],
        metadata: Dict[str, Any],
        measurement_id: Optional[str] = None
    ) -> MeasurementResult:
        """
        Create complete measurement with uncertainty budget
        
        Args:
            value: Measured numerical value
            unit: Physical unit symbol
            uncertainty_components: List of uncertainty component specifications
            metadata: Measurement metadata
            measurement_id: Optional custom measurement ID
            
        Returns:
            Complete MeasurementResult with uncertainty analysis
        """
        
        if measurement_id is None:
            measurement_id = str(uuid.uuid4())
        
        # Validate unit
        unit_obj = unit_registry.get_unit(unit)
        if not unit_obj:
            raise ValueError(f"Unknown unit: {unit}")
        
        # Create uncertainty budget
        budget = UncertaintyBudget(measurement_id)
        
        for comp_spec in uncertainty_components:
            if comp_spec.get('type') == 'type_a':
                await self._add_type_a_component(budget, comp_spec)
            elif comp_spec.get('type') == 'type_b':
                await self._add_type_b_component(budget, comp_spec)
            else:
                raise ValueError(f"Unknown uncertainty type: {comp_spec.get('type')}")
        
        # Create measurement metadata
        measurement_metadata = MeasurementMetadata(
            operator_id=metadata.get('operator_id', 'unknown'),
            procedure_id=metadata.get('procedure_id', 'standard'),
            instrument_id=metadata.get('instrument_id', 'unknown'),
            calibration_date=metadata.get('calibration_date'),
            environmental_conditions=metadata.get('environmental_conditions', {}),
            measurement_method=metadata.get('measurement_method', ''),
            reference_standards=metadata.get('reference_standards', []),
            quality_indicators=metadata.get('quality_indicators', {})
        )
        
        # Create measurement result
        measurement = MeasurementResult(
            measurement_id=measurement_id,
            value=value,
            unit=unit,
            uncertainty_budget=budget,
            metadata=measurement_metadata,
            method=metadata.get('method', ''),
            traceability_chain=metadata.get('traceability_chain', []),
            raw_data=metadata.get('raw_data')
        )
        
        # Cache measurement
        self._measurements_cache[measurement_id] = measurement
        
        # Store in ledger if available
        if self.ledger_service:
            await self._store_measurement_in_ledger(measurement)
        
        logger.info(f"Created measurement {measurement_id}: {measurement.format_result()}")
        return measurement
    
    async def _add_type_a_component(self, budget: UncertaintyBudget, spec: Dict[str, Any]):
        """Add Type A uncertainty component from observations"""
        
        observations = spec.get('observations', [])
        if not observations:
            raise ValueError("Type A component requires observations")
        
        budget.add_type_a_component(
            component_id=spec.get('component_id', f"type_a_{len(budget.components)}"),
            observations=observations,
            description=spec.get('description', ''),
            sensitivity_coefficient=spec.get('sensitivity_coefficient', 1.0)
        )
    
    async def _add_type_b_component(self, budget: UncertaintyBudget, spec: Dict[str, Any]):
        """Add Type B uncertainty component from specification"""
        
        half_width = spec.get('half_width')
        if half_width is None:
            raise ValueError("Type B component requires half_width")
        
        from core.qtmp.uncertainty.uncertainty_budget import DistributionType
        
        distribution_map = {
            'normal': DistributionType.NORMAL,
            'uniform': DistributionType.UNIFORM,
            'triangular': DistributionType.TRIANGULAR,
            'u_shaped': DistributionType.U_SHAPED
        }
        
        distribution = distribution_map.get(
            spec.get('distribution', 'uniform'), 
            DistributionType.UNIFORM
        )
        
        budget.add_type_b_component(
            component_id=spec.get('component_id', f"type_b_{len(budget.components)}"),
            half_width=half_width,
            distribution=distribution,
            description=spec.get('description', ''),
            sensitivity_coefficient=spec.get('sensitivity_coefficient', 1.0),
            degrees_of_freedom=spec.get('degrees_of_freedom')
        )
    
    async def _store_measurement_in_ledger(self, measurement: MeasurementResult):
        """Store measurement in A2 Ledger for persistence"""
        
        try:
            measurement_data = measurement.to_dict()
            
            await self.ledger_service.record_event(
                event_type="qtmp_measurement",
                case_id=measurement.measurement_id,
                payload=measurement_data,
                document_hash=measurement.verification_hash,
                actor=measurement.metadata.operator_id
            )
            
            logger.info(f"Stored measurement {measurement.measurement_id} in ledger")
            
        except Exception as e:
            logger.error(f"Failed to store measurement in ledger: {e}")
            # Don't fail the measurement creation if ledger storage fails
    
    async def get_measurement(self, measurement_id: str) -> Optional[MeasurementResult]:
        """Retrieve measurement by ID"""
        
        # Check cache first
        if measurement_id in self._measurements_cache:
            return self._measurements_cache[measurement_id]
        
        # Try to load from ledger (simplified - just return None for now)
        # PostgreSQLLedger doesn't have direct query_events method
        return None
    
    async def verify_measurement(self, measurement: MeasurementResult) -> Dict[str, Any]:
        """
        Verify measurement integrity and validity
        
        Returns:
            Verification report with status and details
        """
        
        verification_result = {
            'measurement_id': measurement.measurement_id,
            'timestamp': datetime.now(timezone.utc).isoformat(),
            'valid': True,
            'checks': {},
            'warnings': [],
            'errors': []
        }
        
        # Check hash integrity
        expected_hash = measurement._calculate_hash()
        if measurement.verification_hash != expected_hash:
            verification_result['valid'] = False
            verification_result['errors'].append("Hash verification failed - measurement may be tampered")
        
        verification_result['checks']['hash_integrity'] = measurement.verification_hash == expected_hash
        
        # Check unit validity
        unit_valid = unit_registry.get_unit(measurement.unit) is not None
        verification_result['checks']['unit_valid'] = unit_valid
        
        if not unit_valid:
            verification_result['valid'] = False
            verification_result['errors'].append(f"Invalid unit: {measurement.unit}")
        
        # Check uncertainty budget
        try:
            combined = measurement.uncertainty_budget.calculate_combined_uncertainty()
            verification_result['checks']['uncertainty_calculation'] = True
            
            # Check for reasonable uncertainty
            if measurement.value != 0:
                uncertainty_ratio = combined['combined_standard_uncertainty'] / abs(measurement.value)
                if uncertainty_ratio > 0.5:
                    verification_result['warnings'].append(f"Large uncertainty ratio: {uncertainty_ratio:.2f}")
                
                verification_result['checks']['uncertainty_ratio'] = uncertainty_ratio
                
        except Exception as e:
            verification_result['valid'] = False
            verification_result['errors'].append(f"Uncertainty calculation error: {e}")
            verification_result['checks']['uncertainty_calculation'] = False
        
        # Check metadata completeness
        metadata_complete = all([
            measurement.metadata.operator_id,
            measurement.metadata.procedure_id,
            measurement.metadata.instrument_id
        ])
        verification_result['checks']['metadata_complete'] = metadata_complete
        
        if not metadata_complete:
            verification_result['warnings'].append("Incomplete metadata")
        
        # Check timestamp validity
        timestamp_valid = measurement.timestamp <= datetime.now(timezone.utc)
        verification_result['checks']['timestamp_valid'] = timestamp_valid
        
        if not timestamp_valid:
            verification_result['errors'].append("Future timestamp detected")
            verification_result['valid'] = False
        
        return verification_result
    
    async def convert_measurement_unit(
        self, 
        measurement_id: str, 
        target_unit: str
    ) -> Optional[MeasurementResult]:
        """Convert measurement to different unit"""
        
        measurement = await self.get_measurement(measurement_id)
        if not measurement:
            return None
        
        converted = measurement.convert_to_unit(target_unit)
        
        if converted:
            # Cache converted measurement
            self._measurements_cache[converted.measurement_id] = converted
            
            # Store in ledger if available
            if self.ledger_service:
                await self._store_measurement_in_ledger(converted)
        
        return converted
    
    async def batch_create_measurements(
        self, 
        measurements_data: List[Dict[str, Any]]
    ) -> List[Dict[str, Any]]:
        """
        Create multiple measurements in batch
        
        Args:
            measurements_data: List of measurement specifications
            
        Returns:
            List of creation results with success/error status
        """
        
        results = []
        
        for i, data in enumerate(measurements_data):
            try:
                measurement = await self.create_measurement(
                    value=data['value'],
                    unit=data['unit'],
                    uncertainty_components=data['uncertainty_components'],
                    metadata=data['metadata'],
                    measurement_id=data.get('measurement_id')
                )
                
                results.append({
                    'index': i,
                    'success': True,
                    'measurement_id': measurement.measurement_id,
                    'formatted_result': measurement.format_result()
                })
                
            except Exception as e:
                results.append({
                    'index': i,
                    'success': False,
                    'error': str(e),
                    'data': data
                })
                logger.error(f"Batch measurement creation failed at index {i}: {e}")
        
        logger.info(f"Batch created {len([r for r in results if r['success']])} out of {len(measurements_data)} measurements")
        return results
    
    async def get_measurement_statistics(self) -> Dict[str, Any]:
        """Get service statistics"""
        
        total_measurements = len(self._measurements_cache)
        
        unit_distribution = {}
        uncertainty_types = {'type_a': 0, 'type_b': 0, 'combined': 0}
        
        for measurement in self._measurements_cache.values():
            # Count units
            unit_distribution[measurement.unit] = unit_distribution.get(measurement.unit, 0) + 1
            
            # Count uncertainty types
            for comp in measurement.uncertainty_budget.components.values():
                if comp.uncertainty_type == UncertaintyType.TYPE_A:
                    uncertainty_types['type_a'] += 1
                elif comp.uncertainty_type == UncertaintyType.TYPE_B:
                    uncertainty_types['type_b'] += 1
        
        return {
            'total_measurements': total_measurements,
            'unit_distribution': unit_distribution,
            'uncertainty_component_types': uncertainty_types,
            'cache_size': len(self._measurements_cache),
            'ledger_enabled': self.ledger_service is not None
        }