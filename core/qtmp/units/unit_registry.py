# CERTEUS Engine - A5 QTMP Units Management
# Quantum-Resistance Temporal & Metrology Protocol
# Units: SI/UCUM support with conversion and validation

from dataclasses import dataclass
from enum import Enum
import logging
from typing import Any

logger = logging.getLogger(__name__)


class UnitSystem(Enum):
    """Supported unit systems"""

    SI = "si"
    UCUM = "ucum"
    IMPERIAL = "imperial"
    CGS = "cgs"


@dataclass
class Unit:
    """
    Universal unit representation supporting SI/UCUM standards

    Attributes:
        symbol: Unit symbol (e.g., 'm', 'kg', 's', 'mol/L')
        name: Human readable name
        system: Unit system (SI, UCUM, etc.)
        dimension: Physical dimension vector [L,M,T,I,Θ,N,J]
        conversion_factor: Factor to convert to base SI units
        ucum_code: UCUM standardized code if applicable
    """

    symbol: str
    name: str
    system: UnitSystem
    dimension: tuple[int, int, int, int, int, int, int]  # [L,M,T,I,Θ,N,J]
    conversion_factor: float = 1.0
    ucum_code: str | None = None
    aliases: list[str] | None = None

    def __post_init__(self):
        if self.aliases is None:
            self.aliases = []


class UnitRegistry:
    """
    Enterprise-grade unit registry with SI/UCUM support

    Features:
    - SI base and derived units
    - UCUM standardized units
    - Unit conversion and validation
    - Dimensional analysis
    - Parse complex unit expressions
    """

    def __init__(self):
        self._units: dict[str, Unit] = {}
        self._ucum_mappings: dict[str, str] = {}
        self._initialize_base_units()
        self._initialize_derived_units()
        self._initialize_ucum_units()

    def _initialize_base_units(self):
        """Initialize SI base units"""

        # SI Base Units
        base_units = [
            Unit("m", "meter", UnitSystem.SI, (1, 0, 0, 0, 0, 0, 0), 1.0, "m"),
            Unit("kg", "kilogram", UnitSystem.SI, (0, 1, 0, 0, 0, 0, 0), 1.0, "kg"),
            Unit("s", "second", UnitSystem.SI, (0, 0, 1, 0, 0, 0, 0), 1.0, "s"),
            Unit("A", "ampere", UnitSystem.SI, (0, 0, 0, 1, 0, 0, 0), 1.0, "A"),
            Unit("K", "kelvin", UnitSystem.SI, (0, 0, 0, 0, 1, 0, 0), 1.0, "K"),
            Unit("mol", "mole", UnitSystem.SI, (0, 0, 0, 0, 0, 1, 0), 1.0, "mol"),
            Unit("cd", "candela", UnitSystem.SI, (0, 0, 0, 0, 0, 0, 1), 1.0, "cd"),
        ]

        for unit in base_units:
            self._register_unit(unit)

    def _initialize_derived_units(self):
        """Initialize common SI derived units"""

        derived_units = [
            # Area and Volume
            Unit("m²", "square meter", UnitSystem.SI, (2, 0, 0, 0, 0, 0, 0), 1.0, "m2"),
            Unit("m³", "cubic meter", UnitSystem.SI, (3, 0, 0, 0, 0, 0, 0), 1.0, "m3"),
            Unit("L", "liter", UnitSystem.SI, (3, 0, 0, 0, 0, 0, 0), 0.001, "L"),
            # Force and Energy
            Unit("N", "newton", UnitSystem.SI, (1, 1, -2, 0, 0, 0, 0), 1.0, "N"),
            Unit("J", "joule", UnitSystem.SI, (2, 1, -2, 0, 0, 0, 0), 1.0, "J"),
            Unit("W", "watt", UnitSystem.SI, (2, 1, -3, 0, 0, 0, 0), 1.0, "W"),
            # Pressure and Frequency
            Unit("Pa", "pascal", UnitSystem.SI, (-1, 1, -2, 0, 0, 0, 0), 1.0, "Pa"),
            Unit("Hz", "hertz", UnitSystem.SI, (0, 0, -1, 0, 0, 0, 0), 1.0, "Hz"),
            # Electrical
            Unit("V", "volt", UnitSystem.SI, (2, 1, -3, -1, 0, 0, 0), 1.0, "V"),
            Unit("Ω", "ohm", UnitSystem.SI, (2, 1, -3, -2, 0, 0, 0), 1.0, "Ohm"),
            Unit("C", "coulomb", UnitSystem.SI, (0, 0, 1, 1, 0, 0, 0), 1.0, "C"),
            # Common prefixed units
            Unit("mm", "millimeter", UnitSystem.SI, (1, 0, 0, 0, 0, 0, 0), 0.001, "mm"),
            Unit("cm", "centimeter", UnitSystem.SI, (1, 0, 0, 0, 0, 0, 0), 0.01, "cm"),
            Unit("km", "kilometer", UnitSystem.SI, (1, 0, 0, 0, 0, 0, 0), 1000.0, "km"),
            Unit("g", "gram", UnitSystem.SI, (0, 1, 0, 0, 0, 0, 0), 0.001, "g"),
            Unit("mg", "milligram", UnitSystem.SI, (0, 1, 0, 0, 0, 0, 0), 1e-6, "mg"),
        ]

        for unit in derived_units:
            self._register_unit(unit)

    def _initialize_ucum_units(self):
        """Initialize UCUM standardized units for medical/scientific use"""

        ucum_units = [
            # UCUM specific units
            Unit("mol/L", "molar concentration", UnitSystem.UCUM, (-3, 0, 0, 0, 0, 1, 0), 1000.0, "mol/L"),
            Unit("g/L", "grams per liter", UnitSystem.UCUM, (-3, 1, 0, 0, 0, 0, 0), 1.0, "g/L"),
            Unit("mg/dL", "milligrams per deciliter", UnitSystem.UCUM, (-3, 1, 0, 0, 0, 0, 0), 10.0, "mg/dL"),
            Unit("µg/mL", "micrograms per milliliter", UnitSystem.UCUM, (-3, 1, 0, 0, 0, 0, 0), 1.0, "ug/mL"),
            Unit("U/L", "units per liter", UnitSystem.UCUM, (-3, 0, 0, 0, 0, 0, 0), 1.0, "U/L"),
            Unit("°C", "degree Celsius", UnitSystem.UCUM, (0, 0, 0, 0, 1, 0, 0), 1.0, "Cel", ["C"]),
            Unit("min", "minute", UnitSystem.UCUM, (0, 0, 1, 0, 0, 0, 0), 60.0, "min"),
            Unit("h", "hour", UnitSystem.UCUM, (0, 0, 1, 0, 0, 0, 0), 3600.0, "h"),
        ]

        for unit in ucum_units:
            self._register_unit(unit)

    def _register_unit(self, unit: Unit):
        """Register a unit in the registry"""
        self._units[unit.symbol] = unit

        # Register aliases
        if unit.aliases:
            for alias in unit.aliases:
                self._units[alias] = unit

        # Register UCUM code mapping
        if unit.ucum_code:
            self._ucum_mappings[unit.ucum_code] = unit.symbol

    def get_unit(self, symbol: str) -> Unit | None:
        """Get unit by symbol or UCUM code"""
        # Direct lookup
        if symbol in self._units:
            return self._units[symbol]

        # UCUM code lookup
        if symbol in self._ucum_mappings:
            return self._units[self._ucum_mappings[symbol]]

        return None

    def parse_unit_expression(self, expression: str) -> dict[str, Any] | None:
        """
        Parse complex unit expressions like 'kg*m/s²' or 'mol/L'

        Returns:
            Dict with parsed units and powers, or None if invalid
        """
        try:
            # Simple unit
            if expression in self._units:
                return {
                    'units': [(self._units[expression], 1)],
                    'dimension': self._units[expression].dimension,
                    'conversion_factor': self._units[expression].conversion_factor,
                }

            # Handle basic division cases like mol/L, g/L, mg/dL
            if '/' in expression and '*' not in expression:
                parts = expression.split('/')
                if len(parts) == 2:
                    numerator = self.get_unit(parts[0].strip())
                    denominator = self.get_unit(parts[1].strip())

                    if numerator and denominator:
                        # Calculate combined dimension
                        dim = tuple(numerator.dimension[i] - denominator.dimension[i] for i in range(7))

                        conversion = numerator.conversion_factor / denominator.conversion_factor

                        return {
                            'units': [(numerator, 1), (denominator, -1)],
                            'dimension': dim,
                            'conversion_factor': conversion,
                        }

            logger.warning(f"Complex unit expression parsing not fully implemented: {expression}")
            return None

        except Exception as e:
            logger.error(f"Error parsing unit expression '{expression}': {e}")
            return None

    def are_compatible(self, unit1: str, unit2: str) -> bool:
        """Check if two units have compatible dimensions"""
        u1 = self.get_unit(unit1)
        u2 = self.get_unit(unit2)

        if not u1 or not u2:
            return False

        return u1.dimension == u2.dimension

    def convert_value(self, value: float, from_unit: str, to_unit: str) -> float | None:
        """Convert value between compatible units"""
        if not self.are_compatible(from_unit, to_unit):
            return None

        u1 = self.get_unit(from_unit)
        u2 = self.get_unit(to_unit)

        if not u1 or not u2:
            return None

        # Convert to SI base, then to target unit
        si_value = value * u1.conversion_factor
        target_value = si_value / u2.conversion_factor

        # Handle temperature conversion (Celsius to Kelvin)
        if u1.symbol == "°C" and u2.symbol == "K":
            return target_value + 273.15
        elif u1.symbol == "K" and u2.symbol == "°C":
            return target_value - 273.15

        return target_value

    def list_units(self, system: UnitSystem | None = None) -> list[Unit]:
        """List all units, optionally filtered by system"""
        units = list(set(self._units.values()))  # Remove duplicates from aliases

        if system:
            units = [u for u in units if u.system == system]

        return sorted(units, key=lambda u: u.symbol)


# Global registry instance
unit_registry = UnitRegistry()
