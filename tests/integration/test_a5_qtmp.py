# CERTEUS Engine - A5 QTMP Integration Tests
# Quantum-Resistance Temporal & Metrology Protocol
# Tests: Complete DoD validation for measurement system

import asyncio
import math
import uuid
from datetime import datetime, timezone
from typing import Any, Dict, List

import pytest
import pytest_asyncio

from core.qtmp.measurements.measurement_model import (
    MeasurementMetadata, MeasurementResult, create_simple_measurement)
from core.qtmp.uncertainty.uncertainty_budget import (DistributionType,
                                                      UncertaintyBudget,
                                                      UncertaintyComponent,
                                                      UncertaintyType)
# Import A5 QTMP components
from core.qtmp.units.unit_registry import Unit, UnitSystem, unit_registry
from services.qtmp_service.qtmp_service import QTMPService


class TestUnitRegistry:
    """Test A5 unit registry functionality"""
    
    def test_si_base_units(self):
        """Test: SI base units available and properly configured"""
        
        si_base = ['m', 'kg', 's', 'A', 'K', 'mol', 'cd']
        
        for unit_symbol in si_base:
            unit = unit_registry.get_unit(unit_symbol)
            assert unit is not None, f"SI base unit {unit_symbol} not found"
            assert unit.system == UnitSystem.SI
            assert unit.conversion_factor == 1.0  # Base units have factor 1.0
    
    def test_derived_units(self):
        """Test: SI derived units with correct dimensions"""
        
        # Test Newton (force): kg⋅m⋅s⁻²
        newton = unit_registry.get_unit('N')
        assert newton is not None
        assert newton.dimension == (1, 1, -2, 0, 0, 0, 0)  # [L,M,T,I,Θ,N,J]
        
        # Test Joule (energy): kg⋅m²⋅s⁻²
        joule = unit_registry.get_unit('J')
        assert joule is not None
        assert joule.dimension == (2, 1, -2, 0, 0, 0, 0)
        
        # Test Pascal (pressure): kg⋅m⁻¹⋅s⁻²
        pascal = unit_registry.get_unit('Pa')
        assert pascal is not None
        assert pascal.dimension == (-1, 1, -2, 0, 0, 0, 0)
    
    def test_ucum_units(self):
        """Test: UCUM units for medical/scientific applications"""
        
        # Test molar concentration
        mol_l = unit_registry.get_unit('mol/L')
        assert mol_l is not None
        assert mol_l.system == UnitSystem.UCUM
        assert mol_l.ucum_code == 'mol/L'
        
        # Test medical units
        mg_dl = unit_registry.get_unit('mg/dL')
        assert mg_dl is not None
        assert mg_dl.system == UnitSystem.UCUM
    
    def test_unit_conversion(self):
        """Test: Unit conversion functionality"""
        
        # Length conversion
        result = unit_registry.convert_value(1000, 'mm', 'm')
        assert result == 1.0
        
        result = unit_registry.convert_value(1, 'km', 'm')
        assert result == 1000.0
        
        # Mass conversion
        result = unit_registry.convert_value(1000, 'g', 'kg')
        assert result == 1.0
        
        # Temperature conversion (special case)
        result = unit_registry.convert_value(0, '°C', 'K')
        assert result == 273.15
    
    def test_unit_compatibility(self):
        """Test: Unit compatibility checking"""
        
        # Compatible units (length)
        assert unit_registry.are_compatible('m', 'mm') is True
        assert unit_registry.are_compatible('m', 'km') is True
        
        # Incompatible units
        assert unit_registry.are_compatible('m', 'kg') is False
        assert unit_registry.are_compatible('s', 'A') is False
        
        # Same units
        assert unit_registry.are_compatible('m', 'm') is True

class TestUncertaintyBudget:
    """Test A5 uncertainty analysis functionality"""
    
    def test_type_a_uncertainty(self):
        """Test: Type A uncertainty from repeated observations"""
        
        budget = UncertaintyBudget("test_measurement")
        
        # Simulated repeated measurements
        observations = [10.02, 10.01, 9.99, 10.03, 9.98, 10.00, 10.01]
        
        component = budget.add_type_a_component(
            component_id="repeatability",
            observations=observations,
            description="Repeatability of measurement",
            sensitivity_coefficient=1.0
        )
        
        assert component.uncertainty_type == UncertaintyType.TYPE_A
        assert component.degrees_of_freedom == len(observations) - 1
        assert component.value > 0  # Should have some uncertainty
        
        # Verify calculation is reasonable
        n = len(observations)
        mean = sum(observations) / n
        variance = sum((x - mean) ** 2 for x in observations) / (n - 1)
        expected_uncertainty = math.sqrt(variance / n)
        
        assert abs(component.value - expected_uncertainty) < 1e-10
    
    def test_type_b_uncertainty(self):
        """Test: Type B uncertainty from specifications"""
        
        budget = UncertaintyBudget("test_measurement")
        
        # Uniform distribution: ±0.1 range
        component = budget.add_type_b_component(
            component_id="calibration",
            half_width=0.1,
            distribution=DistributionType.UNIFORM,
            description="Calibration certificate uncertainty"
        )
        
        assert component.uncertainty_type == UncertaintyType.TYPE_B
        assert component.distribution == DistributionType.UNIFORM
        
        # For uniform distribution: standard_uncertainty = half_width / sqrt(3)
        expected_uncertainty = 0.1 / math.sqrt(3)
        assert abs(component.value - expected_uncertainty) < 1e-10
    
    def test_combined_uncertainty_calculation(self):
        """Test: GUM law of propagation for combined uncertainty"""
        
        budget = UncertaintyBudget("test_measurement")
        
        # Add multiple components
        budget.add_type_b_component("resolution", 0.05, DistributionType.UNIFORM, "Instrument resolution")
        budget.add_type_b_component("calibration", 0.02, DistributionType.NORMAL, "Calibration uncertainty")
        budget.add_type_b_component("drift", 0.01, DistributionType.UNIFORM, "Drift uncertainty")
        
        combined = budget.calculate_combined_uncertainty()
        
        assert 'combined_standard_uncertainty' in combined
        assert 'expanded_uncertainty' in combined
        assert 'coverage_factor' in combined
        assert 'effective_degrees_of_freedom' in combined
        
        # Combined uncertainty should be larger than individual components
        assert combined['combined_standard_uncertainty'] > 0
        assert combined['expanded_uncertainty'] > combined['combined_standard_uncertainty']
    
    def test_correlation_effects(self):
        """Test: Correlation between uncertainty components"""
        
        budget = UncertaintyBudget("test_measurement")
        
        budget.add_type_b_component("temp_effect", 0.05, DistributionType.NORMAL, "Temperature effect")
        budget.add_type_b_component("humidity_effect", 0.03, DistributionType.NORMAL, "Humidity effect")
        
        # Without correlation
        combined_no_corr = budget.calculate_combined_uncertainty()
        
        # With positive correlation (same environmental chamber)
        budget.set_correlation("temp_effect", "humidity_effect", 0.8)
        combined_with_corr = budget.calculate_combined_uncertainty()
        
        # Positive correlation should increase combined uncertainty
        assert combined_with_corr['combined_standard_uncertainty'] > combined_no_corr['combined_standard_uncertainty']

class TestMeasurementModel:
    """Test A5 measurement model functionality"""
    
    def test_simple_measurement_creation(self):
        """Test: Create simple measurement with uncertainty"""
        
        measurement = create_simple_measurement(
            value=25.3,
            unit="°C",
            uncertainty=0.5,  # ±0.5°C expanded uncertainty
            operator_id="operator_001",
            procedure_id="temp_procedure_v1.2",
            instrument_id="thermometer_001"
        )
        
        assert measurement.value == 25.3
        assert measurement.unit == "°C"
        assert measurement.metadata.operator_id == "operator_001"
        assert measurement.verification_hash is not None
        
        # Check formatted result
        formatted = measurement.format_result("standard")
        assert "25.3" in formatted
        assert "°C" in formatted
        assert "±" in formatted
    
    def test_measurement_validation(self):
        """Test: Measurement validation logic"""
        
        # Valid measurement
        measurement = create_simple_measurement(10.0, "m", 0.1)
        # Should not raise exception
        
        # Test invalid unit (should raise ValueError)
        with pytest.raises(ValueError, match="Unknown unit"):
            create_simple_measurement(10.0, "invalid_unit", 0.1)
    
    def test_measurement_hash_integrity(self):
        """Test: Measurement hash for integrity verification"""
        
        measurement = create_simple_measurement(10.0, "m", 0.1, "op1", "proc1", "inst1")
        original_hash = measurement.verification_hash
        
        # Hash should be deterministic
        recalculated_hash = measurement._calculate_hash()
        assert original_hash == recalculated_hash
        
        # Changing value should change hash
        measurement.value = 11.0
        measurement.verification_hash = measurement._calculate_hash()
        assert measurement.verification_hash != original_hash
    
    def test_unit_conversion(self):
        """Test: Measurement unit conversion"""
        
        # Create measurement in meters
        measurement = create_simple_measurement(1.5, "m", 0.01)  # 1.5 m ± 0.01 m
        
        # Convert to millimeters
        converted = measurement.convert_to_unit("mm")
        
        assert converted is not None
        assert converted.value == 1500.0  # 1.5 m = 1500 mm
        assert converted.unit == "mm"
        
        # Uncertainty should be scaled
        original_expanded = measurement.get_expanded_uncertainty()
        converted_expanded = converted.get_expanded_uncertainty()
        
        # Uncertainty should be scaled by 1000 (m to mm)
        expected_uncertainty = original_expanded['expanded_uncertainty'] * 1000
        actual_uncertainty = converted_expanded['expanded_uncertainty']
        assert abs(actual_uncertainty - expected_uncertainty) < 1e-6
    
    def test_uncertainty_contributions(self):
        """Test: Uncertainty contribution breakdown"""
        
        measurement = create_simple_measurement(100.0, "kg", 2.0)
        contributions = measurement.get_uncertainty_contributions()
        
        assert len(contributions) > 0
        assert all('component_id' in contrib for contrib in contributions)
        assert all('contribution_percent' in contrib for contrib in contributions)
        
        # Total percentage should be approximately 100%
        total_percent = sum(contrib['contribution_percent'] for contrib in contributions)
        assert abs(total_percent - 100.0) < 1e-6

@pytest.mark.asyncio
class TestQTMPService:
    """Test A5 QTMP service functionality"""
    
    async def test_service_initialization(self):
        """Test: QTMP service initialization"""
        
        service = QTMPService()
        assert service.ledger_service is None
        assert len(service._measurements_cache) == 0
    
    async def test_measurement_creation_via_service(self):
        """Test: Create measurement through service API"""
        
        service = QTMPService()
        
        uncertainty_components = [
            {
                'type': 'type_b',
                'component_id': 'resolution',
                'half_width': 0.05,
                'distribution': 'uniform',
                'description': 'Digital display resolution'
            },
            {
                'type': 'type_b',
                'component_id': 'calibration',
                'half_width': 0.02,
                'distribution': 'normal',
                'description': 'Calibration certificate'
            }
        ]
        
        metadata = {
            'operator_id': 'technician_001',
            'procedure_id': 'SOP_001_v2.1',
            'instrument_id': 'balance_001',
            'environmental_conditions': {'temperature': 20.5, 'humidity': 45.2},
            'method': 'Direct weighing'
        }
        
        measurement = await service.create_measurement(
            value=125.67,
            unit="g",
            uncertainty_components=uncertainty_components,
            metadata=metadata
        )
        
        assert measurement.value == 125.67
        assert measurement.unit == "g"
        assert len(measurement.uncertainty_budget.components) == 2
        assert measurement.measurement_id in service._measurements_cache
    
    async def test_measurement_verification(self):
        """Test: Measurement verification functionality"""
        
        service = QTMPService()
        
        # Create measurement
        measurement = create_simple_measurement(10.0, "m", 0.1)
        
        # Verify measurement
        verification = await service.verify_measurement(measurement)
        
        assert verification['valid'] is True
        assert 'checks' in verification
        assert verification['checks']['hash_integrity'] is True
        assert verification['checks']['unit_valid'] is True
        assert verification['checks']['uncertainty_calculation'] is True
    
    async def test_batch_measurement_creation(self):
        """Test: Batch processing of measurements"""
        
        service = QTMPService()
        
        batch_data = [
            {
                'value': 10.1,
                'unit': 'm',
                'uncertainty_components': [{'type': 'type_b', 'half_width': 0.05, 'distribution': 'uniform'}],
                'metadata': {'operator_id': 'op1', 'procedure_id': 'proc1', 'instrument_id': 'inst1'}
            },
            {
                'value': 25.3,
                'unit': '°C',
                'uncertainty_components': [{'type': 'type_b', 'half_width': 0.1, 'distribution': 'normal'}],
                'metadata': {'operator_id': 'op2', 'procedure_id': 'proc2', 'instrument_id': 'inst2'}
            }
        ]
        
        results = await service.batch_create_measurements(batch_data)
        
        assert len(results) == 2
        assert all(result['success'] for result in results)
        assert len(service._measurements_cache) == 2
    
    async def test_service_statistics(self):
        """Test: Service statistics collection"""
        
        service = QTMPService()
        
        # Create some measurements
        await service.create_measurement(
            value=10.0, unit="m",
            uncertainty_components=[{'type': 'type_b', 'half_width': 0.1}],
            metadata={'operator_id': 'op1', 'procedure_id': 'proc1', 'instrument_id': 'inst1'}
        )
        
        await service.create_measurement(
            value=20.0, unit="m",
            uncertainty_components=[{'type': 'type_b', 'half_width': 0.1}],
            metadata={'operator_id': 'op2', 'procedure_id': 'proc2', 'instrument_id': 'inst2'}
        )
        
        stats = await service.get_measurement_statistics()
        
        assert stats['total_measurements'] == 2
        assert 'm' in stats['unit_distribution']
        assert stats['unit_distribution']['m'] == 2
        assert stats['uncertainty_component_types']['type_b'] == 2

class TestDoD:
    """DoD (Definition of Done) validation tests for A5 QTMP"""
    
    @pytest.mark.asyncio
    async def test_dod_e2e_csv_to_verification(self):
        """
        Test: E2E workflow from CSV simulator to verification
        DoD: CSV symulator → Measurement → Bundle → Public → Verify (offline and API)
        """
        
        service = QTMPService()
        
        # Simulate CSV data input
        csv_data = [
            {'value': 10.05, 'unit': 'm', 'uncertainty': 0.02, 'operator': 'op1'},
            {'value': 25.3, 'unit': '°C', 'uncertainty': 0.5, 'operator': 'op2'},
            {'value': 125.67, 'unit': 'g', 'uncertainty': 0.1, 'operator': 'op3'}
        ]
        
        # Convert CSV to measurements
        measurements = []
        for row in csv_data:
            measurement = create_simple_measurement(
                value=row['value'],
                unit=row['unit'],
                uncertainty=row['uncertainty'],
                operator_id=row['operator']
            )
            measurements.append(measurement)
        
        # Verify each measurement
        verification_results = []
        for measurement in measurements:
            verification = await service.verify_measurement(measurement)
            verification_results.append(verification)
        
        # All measurements should verify successfully
        assert all(result['valid'] for result in verification_results)
        assert len(verification_results) == len(csv_data)
    
    @pytest.mark.asyncio
    async def test_dod_uncertainty_report_in_bundle(self):
        """
        Test: Uncertainty report in bundle with method, k, CL
        DoD: Raport niepewności (metoda, k, CL) w bundlu
        """
        
        measurement = create_simple_measurement(10.0, "m", 0.2)
        
        # Get uncertainty report
        expanded_uncertainty = measurement.get_expanded_uncertainty()
        
        # Should contain required elements
        assert 'expanded_uncertainty' in expanded_uncertainty
        assert 'coverage_factor' in expanded_uncertainty  # k
        assert 'confidence_level' in expanded_uncertainty  # CL
        assert 'effective_degrees_of_freedom' in expanded_uncertainty
        
        # Values should be reasonable
        assert expanded_uncertainty['coverage_factor'] >= 1.0  # k ≥ 1
        assert 0 < expanded_uncertainty['confidence_level'] <= 1  # 0 < CL ≤ 1
        
        # Bundle (to_dict) should contain uncertainty report
        bundle = measurement.to_dict()
        assert 'expanded_uncertainty' in bundle
        assert 'uncertainty_budget_summary' in bundle
        assert 'methodology' in bundle['uncertainty_budget_summary']
    
    @pytest.mark.asyncio
    async def test_dod_measurement_repeatability(self):
        """
        Test: Measurement repeatability and result consistency
        DoD: Powtarzalność wyników
        """
        
        # Create identical measurements
        measurements = []
        for i in range(5):
            measurement = create_simple_measurement(
                value=10.0,
                unit="m", 
                uncertainty=0.1,
                operator_id="test_operator",
                procedure_id="repeatability_test"
            )
            measurements.append(measurement)
        
        # All measurements should have same value and similar uncertainty
        values = [m.value for m in measurements]
        assert all(v == 10.0 for v in values)
        
        # Uncertainty should be consistent
        uncertainties = [m.get_expanded_uncertainty()['expanded_uncertainty'] for m in measurements]
        uncertainty_range = max(uncertainties) - min(uncertainties)
        assert uncertainty_range < 1e-10  # Very small tolerance for identical measurements
    
    @pytest.mark.asyncio
    async def test_dod_si_ucum_integration(self):
        """
        Test: SI/UCUM unit integration
        DoD: Model „Measurement" (SI/UCUM)
        """
        
        # Test SI units
        si_measurement = create_simple_measurement(10.0, "m", 0.01)
        assert si_measurement.unit == "m"
        
        si_unit = unit_registry.get_unit("m")
        assert si_unit.system == UnitSystem.SI
        
        # Test UCUM units
        ucum_measurement = create_simple_measurement(5.0, "mol/L", 0.1)
        assert ucum_measurement.unit == "mol/L"
        
        ucum_unit = unit_registry.get_unit("mol/L")
        assert ucum_unit.system == UnitSystem.UCUM
        
        # Test unit conversion between compatible units
        converted = si_measurement.convert_to_unit("mm")
        assert converted is not None
        assert converted.value == 10000.0  # 10 m = 10000 mm
    
    @pytest.mark.asyncio
    async def test_dod_type_a_b_propagation(self):
        """
        Test: Type A/B uncertainty with propagation
        DoD: Type A/B, propagacja
        """
        
        service = QTMPService()
        
        # Create measurement with both Type A and Type B components
        uncertainty_components = [
            {
                'type': 'type_a',
                'component_id': 'repeatability',
                'observations': [10.01, 9.99, 10.03, 9.97, 10.02, 10.00],
                'description': 'Repeated measurements'
            },
            {
                'type': 'type_b',
                'component_id': 'calibration',
                'half_width': 0.05,
                'distribution': 'normal',
                'description': 'Calibration certificate'
            },
            {
                'type': 'type_b',
                'component_id': 'resolution',
                'half_width': 0.01,
                'distribution': 'uniform',
                'description': 'Instrument resolution'
            }
        ]
        
        measurement = await service.create_measurement(
            value=10.0,
            unit="m",
            uncertainty_components=uncertainty_components,
            metadata={'operator_id': 'op1', 'procedure_id': 'proc1', 'instrument_id': 'inst1'}
        )
        
        # Should have both Type A and Type B components
        budget = measurement.uncertainty_budget
        type_a_components = [c for c in budget.components.values() if c.uncertainty_type == UncertaintyType.TYPE_A]
        type_b_components = [c for c in budget.components.values() if c.uncertainty_type == UncertaintyType.TYPE_B]
        
        assert len(type_a_components) == 1
        assert len(type_b_components) == 2
        
        # Combined uncertainty should follow GUM propagation
        combined = budget.calculate_combined_uncertainty()
        assert combined['calculation_method'] == 'GUM_law_of_propagation'
        assert combined['combined_standard_uncertainty'] > 0
    
    @pytest.mark.asyncio 
    async def test_dod_api_endpoints_simulation(self):
        """
        Test: API endpoints functionality simulation  
        DoD: API: `/v1/qtmp/measurements`, `/v1/qtmp/verify`
        """
        
        service = QTMPService()
        
        # Simulate /v1/qtmp/measurements POST
        measurement_request = {
            'value': 25.5,
            'unit': '°C',
            'uncertainty_components': [
                {'type': 'type_b', 'half_width': 0.1, 'distribution': 'normal'}
            ],
            'metadata': {
                'operator_id': 'api_user_001',
                'procedure_id': 'api_procedure',
                'instrument_id': 'api_instrument'
            }
        }
        
        measurement = await service.create_measurement(**measurement_request)
        assert measurement.measurement_id is not None
        
        # Simulate /v1/qtmp/verify POST
        verification_result = await service.verify_measurement(measurement)
        assert verification_result['valid'] is True
        assert 'checks' in verification_result
        
        # Simulate GET measurement
        retrieved = await service.get_measurement(measurement.measurement_id)
        assert retrieved is not None
        assert retrieved.measurement_id == measurement.measurement_id

# === Test Runner ===

if __name__ == "__main__":
    # Run all tests
    pytest.main([__file__, "-v", "--tb=short"])