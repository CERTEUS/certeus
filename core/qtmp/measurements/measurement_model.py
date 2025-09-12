# CERTEUS Engine - A5 QTMP Measurement Model
# Quantum-Resistance Temporal & Metrology Protocol  
# Measurement: Value + Uncertainty + Full metrological traceability

from dataclasses import dataclass, field
from datetime import UTC, datetime
import hashlib
import json
import logging
from typing import Any, Optional
import uuid

from core.qtmp.uncertainty.uncertainty_budget import UncertaintyBudget
from core.qtmp.units.unit_registry import unit_registry

logger = logging.getLogger(__name__)

@dataclass
class MeasurementMetadata:
    """Metrological metadata for full traceability"""
    operator_id: str
    procedure_id: str
    instrument_id: str
    calibration_date: datetime | None = None
    environmental_conditions: dict[str, Any] = field(default_factory=dict)
    measurement_method: str = ""
    reference_standards: list[str] = field(default_factory=list)
    quality_indicators: dict[str, float] = field(default_factory=dict)

@dataclass 
class MeasurementResult:
    """
    Complete measurement result following QTMP protocol
    
    Core equation: Result = Value ± Uncertainty [Unit] (k=coverage_factor, CL=confidence_level)
    
    Attributes:
        measurement_id: Unique identifier for this measurement
        value: Measured numerical value
        unit: Physical unit (from unit registry)
        uncertainty_budget: Complete uncertainty analysis
        metadata: Metrological traceability information
        timestamp: When measurement was performed
        method: Measurement method/procedure
        traceability_chain: Link to reference standards
    """
    measurement_id: str
    value: float
    unit: str
    uncertainty_budget: UncertaintyBudget
    metadata: MeasurementMetadata
    timestamp: datetime = field(default_factory=lambda: datetime.now(UTC))
    method: str = ""
    traceability_chain: list[str] = field(default_factory=list)
    raw_data: dict[str, Any] | None = None
    verification_hash: str | None = None
    
    def __post_init__(self):
        """Validate measurement and calculate verification hash"""
        self._validate()
        self.verification_hash = self._calculate_hash()
    
    def _validate(self):
        """Validate measurement components"""
        
        # Validate unit exists in registry
        unit_obj = unit_registry.get_unit(self.unit)
        if not unit_obj:
            raise ValueError(f"Unknown unit: {self.unit}")
        
        # Validate uncertainty budget belongs to this measurement
        if self.uncertainty_budget.measurement_id != self.measurement_id:
            raise ValueError("Uncertainty budget measurement_id mismatch")
        
        # Check for reasonable uncertainty relative to value
        try:
            combined = self.uncertainty_budget.calculate_combined_uncertainty()
            uncertainty_ratio = combined['combined_standard_uncertainty'] / abs(self.value) if self.value != 0 else 0
            
            if uncertainty_ratio > 1.0:
                logger.warning(f"Large uncertainty ratio: {uncertainty_ratio:.2f} for {self.measurement_id}")
        except Exception as e:
            logger.error(f"Could not validate uncertainty for {self.measurement_id}: {e}")
    
    def _calculate_hash(self) -> str:
        """Calculate verification hash for measurement integrity"""
        
        # Create deterministic representation
        hash_data = {
            'measurement_id': self.measurement_id,
            'value': self.value,
            'unit': self.unit,
            'timestamp': self.timestamp.isoformat(),
            'method': self.method,
            'operator_id': self.metadata.operator_id,
            'procedure_id': self.metadata.procedure_id,
            'instrument_id': self.metadata.instrument_id
        }
        
        # Include uncertainty budget summary
        try:
            budget_summary = self.uncertainty_budget.get_budget_summary()
            hash_data['uncertainty_components'] = len(budget_summary['components'])
            hash_data['combined_uncertainty'] = budget_summary['combined_uncertainty'].get('combined_standard_uncertainty')
        except Exception as e:
            logger.warning(f"Could not include uncertainty in hash: {e}")
        
        # Calculate SHA-256 hash
        hash_string = json.dumps(hash_data, sort_keys=True, default=str)
        return hashlib.sha256(hash_string.encode()).hexdigest()
    
    def get_expanded_uncertainty(self, confidence_level: float = 0.95) -> dict[str, Any]:
        """Get expanded uncertainty for specified confidence level"""
        
        try:
            combined = self.uncertainty_budget.calculate_combined_uncertainty()
            
            return {
                'expanded_uncertainty': combined['expanded_uncertainty'],
                'coverage_factor': combined['coverage_factor'],
                'confidence_level': confidence_level,
                'effective_degrees_of_freedom': combined['effective_degrees_of_freedom'],
                'unit': self.unit
            }
        except Exception as e:
            logger.error(f"Error calculating expanded uncertainty: {e}")
            return {'error': str(e)}
    
    def format_result(self, format_type: str = "standard") -> str:
        """
        Format measurement result for reporting
        
        Args:
            format_type: "standard", "scientific", "compact", "full"
            
        Returns:
            Formatted measurement result string
        """
        
        try:
            expanded = self.get_expanded_uncertainty()
            
            if 'error' in expanded:
                return f"{self.value} {self.unit} (uncertainty calculation error)"
            
            uncertainty = expanded['expanded_uncertainty']
            coverage_factor = expanded['coverage_factor']
            confidence_level = expanded['confidence_level']
            
            if format_type == "standard":
                return f"{self.value:.3f} ± {uncertainty:.3f} {self.unit} (k={coverage_factor:.2f})"
            
            elif format_type == "scientific":
                return f"{self.value:.2e} ± {uncertainty:.2e} {self.unit} (k={coverage_factor:.2f}, CL={confidence_level:.0%})"
            
            elif format_type == "compact":
                return f"{self.value:.2f}±{uncertainty:.2f} {self.unit}"
            
            elif format_type == "full":
                dof = expanded.get('effective_degrees_of_freedom', 'inf')
                return (f"{self.value:.3f} ± {uncertainty:.3f} {self.unit} "
                       f"(k={coverage_factor:.2f}, νeff={dof:.0f}, CL={confidence_level:.0%})")
            
            else:
                return f"{self.value} ± {uncertainty} {self.unit}"
                
        except Exception as e:
            logger.error(f"Error formatting result: {e}")
            return f"{self.value} {self.unit} (formatting error)"
    
    def convert_to_unit(self, target_unit: str) -> Optional['MeasurementResult']:
        """
        Convert measurement to different compatible unit
        
        Args:
            target_unit: Target unit symbol
            
        Returns:
            New MeasurementResult in target unit or None if incompatible
        """
        
        # Check unit compatibility
        if not unit_registry.are_compatible(self.unit, target_unit):
            logger.error(f"Units {self.unit} and {target_unit} are not compatible")
            return None
        
        # Convert value
        converted_value = unit_registry.convert_value(self.value, self.unit, target_unit)
        if converted_value is None:
            logger.error(f"Could not convert {self.value} from {self.unit} to {target_unit}")
            return None
        
        # Get conversion factor for uncertainty
        unit_from = unit_registry.get_unit(self.unit)
        unit_to = unit_registry.get_unit(target_unit)
        
        if not unit_from or not unit_to:
            return None
        
        conversion_factor = unit_from.conversion_factor / unit_to.conversion_factor
        
        # Create new uncertainty budget with scaled components
        new_budget = UncertaintyBudget(f"{self.measurement_id}_converted_{target_unit}")
        
        for comp_id, comp in self.uncertainty_budget.components.items():
            # Scale uncertainty component by conversion factor
            scaled_comp = UncertaintyComponent(
                component_id=f"{comp_id}_converted",
                value=comp.value * abs(conversion_factor),
                uncertainty_type=comp.uncertainty_type,
                distribution=comp.distribution,
                degrees_of_freedom=comp.degrees_of_freedom,
                sensitivity_coefficient=comp.sensitivity_coefficient,
                description=f"{comp.description} (converted to {target_unit})",
                source=comp.source
            )
            new_budget.add_component(scaled_comp)
        
        # Copy correlations
        new_budget.correlation_matrix = self.uncertainty_budget.correlation_matrix.copy()
        
        # Create new measurement result
        return MeasurementResult(
            measurement_id=f"{self.measurement_id}_converted_{target_unit}",
            value=converted_value,
            unit=target_unit,
            uncertainty_budget=new_budget,
            metadata=self.metadata,
            timestamp=self.timestamp,
            method=f"{self.method} (unit conversion from {self.unit})",
            traceability_chain=self.traceability_chain.copy(),
            raw_data=self.raw_data
        )
    
    def get_uncertainty_contributions(self) -> list[dict[str, Any]]:
        """Get breakdown of uncertainty contributions"""
        
        try:
            combined = self.uncertainty_budget.calculate_combined_uncertainty()
            total_variance = combined['combined_standard_uncertainty'] ** 2
            
            contributions = []
            for comp in self.uncertainty_budget.components.values():
                contribution_variance = (comp.sensitivity_coefficient * comp.value) ** 2
                contribution_percent = (contribution_variance / total_variance * 100) if total_variance > 0 else 0
                
                contributions.append({
                    'component_id': comp.component_id,
                    'type': comp.uncertainty_type.value,
                    'standard_uncertainty': comp.value,
                    'contribution_variance': contribution_variance,
                    'contribution_percent': contribution_percent,
                    'sensitivity_coefficient': comp.sensitivity_coefficient,
                    'description': comp.description
                })
            
            # Sort by contribution percentage
            contributions.sort(key=lambda x: x['contribution_percent'], reverse=True)
            
            return contributions
            
        except Exception as e:
            logger.error(f"Error calculating uncertainty contributions: {e}")
            return []
    
    def to_dict(self) -> dict[str, Any]:
        """Convert measurement result to dictionary for serialization"""
        
        expanded_uncertainty = self.get_expanded_uncertainty()
        uncertainty_contributions = self.get_uncertainty_contributions()
        
        return {
            'measurement_id': self.measurement_id,
            'value': self.value,
            'unit': self.unit,
            'formatted_result': self.format_result("full"),
            'timestamp': self.timestamp.isoformat(),
            'method': self.method,
            'verification_hash': self.verification_hash,
            'expanded_uncertainty': expanded_uncertainty,
            'uncertainty_contributions': uncertainty_contributions,
            'uncertainty_budget_summary': self.uncertainty_budget.get_budget_summary(),
            'metadata': {
                'operator_id': self.metadata.operator_id,
                'procedure_id': self.metadata.procedure_id,
                'instrument_id': self.metadata.instrument_id,
                'calibration_date': self.metadata.calibration_date.isoformat() if self.metadata.calibration_date else None,
                'environmental_conditions': self.metadata.environmental_conditions,
                'measurement_method': self.metadata.measurement_method,
                'reference_standards': self.metadata.reference_standards,
                'quality_indicators': self.metadata.quality_indicators
            },
            'traceability_chain': self.traceability_chain,
            'raw_data': self.raw_data
        }

# Import here to avoid circular import
from core.qtmp.uncertainty.uncertainty_budget import UncertaintyComponent


def create_simple_measurement(
    value: float,
    unit: str,
    uncertainty: float,
    operator_id: str = "unknown",
    procedure_id: str = "standard",
    instrument_id: str = "unknown"
) -> MeasurementResult:
    """
    Create simple measurement with single Type B uncertainty component
    
    Args:
        value: Measured value
        unit: Unit symbol
        uncertainty: Expanded uncertainty (k=2, 95% confidence)
        operator_id: Person performing measurement
        procedure_id: Measurement procedure
        instrument_id: Measuring instrument
        
    Returns:
        Complete MeasurementResult
    """
    
    measurement_id = str(uuid.uuid4())
    
    # Create uncertainty budget with single Type B component
    budget = UncertaintyBudget(measurement_id)
    budget.add_type_b_component(
        component_id="main_uncertainty",
        half_width=uncertainty / 2,  # Convert expanded to half-width
        description="Main measurement uncertainty"
    )
    
    # Create metadata
    metadata = MeasurementMetadata(
        operator_id=operator_id,
        procedure_id=procedure_id,
        instrument_id=instrument_id
    )
    
    return MeasurementResult(
        measurement_id=measurement_id,
        value=value,
        unit=unit,
        uncertainty_budget=budget,
        metadata=metadata
    )