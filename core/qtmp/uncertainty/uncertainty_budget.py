# CERTEUS Engine - A5 QTMP Uncertainty Management  
# Quantum-Resistance Temporal & Metrology Protocol
# Uncertainty: Type A/B analysis with propagation

import logging
import math
from dataclasses import dataclass
from datetime import datetime, timezone
from enum import Enum
from typing import Any, Dict, List, Optional, Union

logger = logging.getLogger(__name__)

class UncertaintyType(Enum):
    """Types of uncertainty according to GUM (Guide to Uncertainty in Measurement)"""
    TYPE_A = "type_a"  # Statistical analysis of repeated observations
    TYPE_B = "type_b"  # Other means (calibration certificates, specifications, etc.)
    COMBINED = "combined"  # Combined standard uncertainty
    EXPANDED = "expanded"  # Expanded uncertainty with coverage factor

class DistributionType(Enum):
    """Probability distributions for Type B uncertainties"""
    NORMAL = "normal"
    UNIFORM = "uniform"  
    TRIANGULAR = "triangular"
    U_SHAPED = "u_shaped"
    CUSTOM = "custom"

@dataclass
class UncertaintyComponent:
    """
    Individual uncertainty component following GUM methodology
    
    Attributes:
        component_id: Unique identifier for this component
        value: Standard uncertainty value
        uncertainty_type: Type A or Type B
        distribution: Probability distribution (for Type B)
        degrees_of_freedom: Statistical degrees of freedom
        sensitivity_coefficient: Partial derivative ∂f/∂xi
        description: Human readable description
        source: Source of uncertainty (instrument, environment, etc.)
    """
    component_id: str
    value: float
    uncertainty_type: UncertaintyType
    distribution: DistributionType = DistributionType.NORMAL
    degrees_of_freedom: Optional[float] = None
    sensitivity_coefficient: float = 1.0
    description: str = ""
    source: str = ""
    confidence_level: float = 0.68  # 1σ for normal distribution

    def __post_init__(self):
        if self.value < 0:
            raise ValueError("Uncertainty value must be non-negative")
        
        if not 0 < self.confidence_level <= 1:
            raise ValueError("Confidence level must be between 0 and 1")

class UncertaintyBudget:
    """
    Complete uncertainty budget for a measurement
    
    Features:
    - Type A/B uncertainty components
    - GUM-compliant uncertainty propagation
    - Welch-Satterthwaite degrees of freedom calculation
    - Coverage factor determination
    - Monte Carlo simulation support
    """
    
    def __init__(self, measurement_id: str):
        self.measurement_id = measurement_id
        self.components: Dict[str, UncertaintyComponent] = {}
        self.correlation_matrix: Dict[tuple[str, str], float] = {}
        self.created_at = datetime.now(timezone.utc)
    
    def add_component(self, component: UncertaintyComponent):
        """Add uncertainty component to budget"""
        if component.component_id in self.components:
            logger.warning(f"Overwriting component {component.component_id}")
        
        self.components[component.component_id] = component
        logger.info(f"Added {component.uncertainty_type.value} component: {component.component_id}")
    
    def add_type_a_component(
        self, 
        component_id: str,
        observations: List[float],
        description: str = "",
        sensitivity_coefficient: float = 1.0
    ) -> UncertaintyComponent:
        """
        Add Type A uncertainty component from repeated observations
        
        Args:
            component_id: Unique identifier
            observations: List of repeated measurements
            description: Description of component
            sensitivity_coefficient: ∂f/∂xi sensitivity coefficient
            
        Returns:
            Created UncertaintyComponent
        """
        if len(observations) < 2:
            raise ValueError("Type A analysis requires at least 2 observations")
        
        n = len(observations)
        mean = sum(observations) / n
        variance = sum((x - mean) ** 2 for x in observations) / (n - 1)
        standard_uncertainty = math.sqrt(variance / n)  # Standard error of mean
        
        component = UncertaintyComponent(
            component_id=component_id,
            value=standard_uncertainty,
            uncertainty_type=UncertaintyType.TYPE_A,
            distribution=DistributionType.NORMAL,
            degrees_of_freedom=n - 1,
            sensitivity_coefficient=sensitivity_coefficient,
            description=description,
            source=f"Statistical analysis of {n} observations"
        )
        
        self.add_component(component)
        return component
    
    def add_type_b_component(
        self,
        component_id: str,
        half_width: float,
        distribution: DistributionType = DistributionType.UNIFORM,
        description: str = "",
        sensitivity_coefficient: float = 1.0,
        degrees_of_freedom: Optional[float] = None
    ) -> UncertaintyComponent:
        """
        Add Type B uncertainty component from specification/certificate
        
        Args:
            component_id: Unique identifier
            half_width: Half-width of uncertainty interval
            distribution: Assumed probability distribution
            description: Description of component
            sensitivity_coefficient: ∂f/∂xi sensitivity coefficient
            degrees_of_freedom: Effective degrees of freedom (if known)
            
        Returns:
            Created UncertaintyComponent
        """
        
        # Convert half-width to standard uncertainty based on distribution
        divisors = {
            DistributionType.UNIFORM: math.sqrt(3),
            DistributionType.TRIANGULAR: math.sqrt(6),
            DistributionType.NORMAL: 2.0,  # Assuming 95% coverage
            DistributionType.U_SHAPED: math.sqrt(2),
        }
        
        divisor = divisors.get(distribution, math.sqrt(3))
        standard_uncertainty = half_width / divisor
        
        # Estimate degrees of freedom for Type B (if not provided)
        if degrees_of_freedom is None:
            # Rough estimate: larger for well-known distributions
            if distribution == DistributionType.NORMAL:
                degrees_of_freedom = 50  # Well-characterized
            elif distribution == DistributionType.UNIFORM:
                degrees_of_freedom = float('inf')  # Infinite for uniform
            else:
                degrees_of_freedom = 10  # Conservative estimate
        
        component = UncertaintyComponent(
            component_id=component_id,
            value=standard_uncertainty,
            uncertainty_type=UncertaintyType.TYPE_B,
            distribution=distribution,
            degrees_of_freedom=degrees_of_freedom,
            sensitivity_coefficient=sensitivity_coefficient,
            description=description,
            source=f"Type B from {distribution.value} distribution"
        )
        
        self.add_component(component)
        return component
    
    def set_correlation(self, component1_id: str, component2_id: str, correlation: float):
        """Set correlation coefficient between two components"""
        if not -1 <= correlation <= 1:
            raise ValueError("Correlation coefficient must be between -1 and 1")
        
        if component1_id not in self.components or component2_id not in self.components:
            raise ValueError("Both components must exist in budget")
        
        key = tuple(sorted([component1_id, component2_id]))
        self.correlation_matrix[key] = correlation
        
        logger.info(f"Set correlation between {component1_id} and {component2_id}: {correlation}")
    
    def calculate_combined_uncertainty(self) -> Dict[str, Any]:
        """
        Calculate combined standard uncertainty using GUM law of propagation
        
        Returns:
            Dict with combined uncertainty, effective degrees of freedom, etc.
        """
        if not self.components:
            raise ValueError("No uncertainty components defined")
        
        # Calculate combined standard uncertainty with correlations
        variance_combined = 0.0
        
        # Individual component contributions
        for comp in self.components.values():
            contribution = (comp.sensitivity_coefficient * comp.value) ** 2
            variance_combined += contribution
        
        # Correlation contributions
        for (id1, id2), corr in self.correlation_matrix.items():
            comp1 = self.components[id1]
            comp2 = self.components[id2]
            
            correlation_term = (
                2 * corr * 
                comp1.sensitivity_coefficient * comp1.value *
                comp2.sensitivity_coefficient * comp2.value
            )
            variance_combined += correlation_term
        
        combined_uncertainty = math.sqrt(variance_combined)
        
        # Calculate effective degrees of freedom (Welch-Satterthwaite formula)
        effective_dof = self._calculate_effective_dof(combined_uncertainty)
        
        # Determine coverage factor for 95% confidence
        coverage_factor = self._get_coverage_factor(effective_dof, 0.95)
        
        # Calculate expanded uncertainty
        expanded_uncertainty = coverage_factor * combined_uncertainty
        
        return {
            'combined_standard_uncertainty': combined_uncertainty,
            'effective_degrees_of_freedom': effective_dof,
            'coverage_factor': coverage_factor,
            'expanded_uncertainty': expanded_uncertainty,
            'confidence_level': 0.95,
            'num_components': len(self.components),
            'calculation_method': 'GUM_law_of_propagation'
        }
    
    def _calculate_effective_dof(self, combined_uncertainty: float) -> float:
        """Calculate effective degrees of freedom using Welch-Satterthwaite formula"""
        if combined_uncertainty == 0:
            return float('inf')
        
        numerator = combined_uncertainty ** 4
        denominator = 0.0
        
        for comp in self.components.values():
            if comp.degrees_of_freedom and comp.degrees_of_freedom > 0:
                contribution = (comp.sensitivity_coefficient * comp.value) ** 4
                denominator += contribution / comp.degrees_of_freedom
        
        if denominator == 0:
            return float('inf')
        
        return numerator / denominator
    
    def _get_coverage_factor(self, degrees_of_freedom: float, confidence_level: float) -> float:
        """Get coverage factor (k) for given degrees of freedom and confidence level"""
        
        # t-distribution values for 95% confidence (approximation)
        t_values = {
            1: 12.71, 2: 4.30, 3: 3.18, 4: 2.78, 5: 2.57,
            6: 2.45, 7: 2.36, 8: 2.31, 9: 2.26, 10: 2.23,
            15: 2.13, 20: 2.09, 30: 2.04, 50: 2.01, 100: 1.98
        }
        
        if abs(confidence_level - 0.95) < 1e-10:
            if degrees_of_freedom == float('inf'):
                return 1.96  # Normal distribution
            
            # Find closest t-value
            dof_int = int(degrees_of_freedom)
            if dof_int in t_values:
                return t_values[dof_int]
            elif dof_int >= 100:
                return 1.96
            else:
                # Linear interpolation for intermediate values
                lower_dof = max([d for d in t_values.keys() if d <= dof_int])
                upper_dof = min([d for d in t_values.keys() if d >= dof_int])
                
                if lower_dof == upper_dof:
                    return t_values[lower_dof]
                
                # Interpolate
                factor = (dof_int - lower_dof) / (upper_dof - lower_dof)
                return t_values[lower_dof] + factor * (t_values[upper_dof] - t_values[lower_dof])
        
        # Default to 2.0 for other confidence levels (conservative)
        return 2.0
    
    def get_budget_summary(self) -> Dict[str, Any]:
        """Get complete uncertainty budget summary"""
        
        try:
            combined_result = self.calculate_combined_uncertainty()
        except Exception as e:
            logger.error(f"Error calculating combined uncertainty: {e}")
            combined_result = {'error': str(e)}
        
        component_details = []
        for comp in self.components.values():
            component_details.append({
                'id': comp.component_id,
                'type': comp.uncertainty_type.value,
                'standard_uncertainty': comp.value,
                'contribution': (comp.sensitivity_coefficient * comp.value) ** 2,
                'sensitivity_coefficient': comp.sensitivity_coefficient,
                'degrees_of_freedom': comp.degrees_of_freedom,
                'distribution': comp.distribution.value,
                'description': comp.description,
                'source': comp.source
            })
        
        return {
            'measurement_id': self.measurement_id,
            'created_at': self.created_at.isoformat(),
            'components': component_details,
            'correlations': dict(self.correlation_matrix),
            'combined_uncertainty': combined_result,
            'methodology': 'GUM_Guide_to_Uncertainty_in_Measurement'
        }