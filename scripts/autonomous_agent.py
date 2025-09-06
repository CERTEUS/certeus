#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/autonomous_agent.py                          |
# | ROLE: Autonomous AI agent execution controller             |
# | PLIK: scripts/autonomous_agent.py                          |
# | ROLA: Kontroler autonomicznego wykonywania AI              |
# +-------------------------------------------------------------+

"""
Autonomous AI Agent Controller
Enables full autonomous operation without manual approvals
"""

import os
import subprocess
import sys


def setup_autonomous_mode():
    """Configure repository for autonomous AI operation"""

    # Git configuration for autonomous commits
    subprocess.run(["git", "config", "user.name", "CERTEUS-AI-Agent"], check=False)
    subprocess.run(
        ["git", "config", "user.email", "ai-agent@certeus.local"], check=False
    )
    subprocess.run(["git", "config", "commit.gpgsign", "true"], check=False)

    # Set autonomous environment variables
    os.environ["CERTEUS_AUTONOMOUS_MODE"] = "true"
    os.environ["AI_AGENT_AUTHORITY"] = "full"
    os.environ["MANUAL_APPROVAL_REQUIRED"] = "false"

    print("✅ Autonomous mode configured")


def autonomous_execute(command_args):
    """Execute command autonomously without approval"""

    print(f"🤖 AUTONOMOUS EXECUTION: {' '.join(command_args)}")

    try:
        result = subprocess.run(
            command_args, capture_output=True, text=True, check=False
        )

        if result.returncode == 0:
            print(f"✅ SUCCESS: {result.stdout}")
        else:
            print(f"⚠️ WARNING: {result.stderr}")

        return result.returncode == 0

    except Exception as e:
        print(f"❌ ERROR: {e}")
        return False


def autonomous_commit_and_push(message):
    """Autonomous commit and push without approval"""

    # Stage all changes
    autonomous_execute(["git", "add", "-A"])

    # Commit with autonomous signature
    commit_msg = (
        f"🤖 AUTONOMOUS: {message}\n\n"
        "Executed by AI Agent without manual approval\n"
        "Full autonomous authority granted by repository owner"
    )
    autonomous_execute(["git", "commit", "-m", commit_msg])

    # Push to origin
    branch = subprocess.run(
        ["git", "branch", "--show-current"], capture_output=True, text=True
    ).stdout.strip()

    autonomous_execute(["git", "push", "origin", branch])

    print(f"✅ Autonomous commit and push completed to {branch}")


if __name__ == "__main__":
    setup_autonomous_mode()

    if len(sys.argv) > 1:
        if sys.argv[1] == "commit":
            message = (
                " ".join(sys.argv[2:]) if len(sys.argv) > 2 else "Autonomous update"
            )
            autonomous_commit_and_push(message)
        else:
            success = autonomous_execute(sys.argv[1:])
            sys.exit(0 if success else 1)
    else:
        print("🤖 CERTEUS Autonomous AI Agent Ready")
        print("✅ Full autonomous authority enabled")
        print("🚀 No manual approvals required")
