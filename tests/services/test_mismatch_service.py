# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/services/test_mismatch_ser|
# | DATE:    2025-08-17                                          |
# +=====================================================================+
"""
PL: Testy jednostkowe / integracyjne modułu.
EN: Module test suite (unit/integration).
"""

# +-------------------------------------------------------------+
# | CERTEUS - Tests: Mismatch Service                           |
# +-------------------------------------------------------------+
from services.mismatch_service.service import MismatchService
from services.mismatch_service.models import TicketResolution, ResolutionType


def test_create_and_resolve_ticket():
    svc = MismatchService()
    t = svc.create_ticket(
        case_id="case-001",
        formula_str="p -> q",
        results={"z3": {"status": "sat"}, "cvc5": {"status": "unsat"}},
    )
    assert t.ticket_id.startswith("MM-")
    assert t.priority in ("high", "critical", "medium", "low")

    res = TicketResolution(
        ticket_id=t.ticket_id,
        resolution_type=ResolutionType.HUMAN_OVERRIDE,
        chosen_result="sat",
        notes="Expert decision",
        resolved_by="tester",
        confidence=0.8,
    )
    t2 = svc.resolve_ticket(t.ticket_id, res)
    assert t2.status == "resolved"
    assert t2.chosen_result == "sat"
