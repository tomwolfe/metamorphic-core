from enum import Enum
from pydantic import BaseModel
from datetime import datetime
from typing import Optional

class ConstraintCategory(Enum):
    BIAS = "bias_mitigation"
    SAFETY = "system_safety"
    TRANSPARENCY = "operational_transparency"
    LEGAL = "legal_compliance"
    PERFORMANCE = "performance_ethics"

class RiskProfile(Enum):
    CRITICAL = 4
    HIGH = 3
    MEDIUM = 2
    LOW = 1
    INFO = 0

class EthicalConstraint(BaseModel):
    name: str
    category: ConstraintCategory
    description: str
    risk_profile: RiskProfile
    enforcement_level: int
    quantum_weight: float = 0.5
    last_violated: Optional[datetime] = None

class EthicalViolation(BaseModel):
    constraint: EthicalConstraint
    violation_timestamp: datetime
    severity: float
    quantum_state_id: str
    resolution_status: str = "unresolved"
    mitigation_plan: Optional[str] = None

# Core constraint definitions
CORE_CONSTRAINTS = [
    EthicalConstraint(
        name="Bias Risk Threshold",
        category=ConstraintCategory.BIAS,
        description="Maximum acceptable bias risk probability",
        risk_profile=RiskProfile.CRITICAL,
        enforcement_level=5,
        quantum_weight=0.4
    ),
    EthicalConstraint(
        name="Safety Boundary",
        category=ConstraintCategory.SAFETY,
        description="System safety operational limits",
        risk_profile=RiskProfile.HIGH,
        enforcement_level=4,
        quantum_weight=0.3
    ),
    EthicalConstraint(
        name="Transparency Minimum",
        category=ConstraintCategory.TRANSPARENCY,
        description="Minimum required transparency score",
        risk_profile=RiskProfile.MEDIUM,
        enforcement_level=3,
        quantum_weight=0.3
    )
]
