"""
Live Agent Visualizer
Integrates with the actual repair agent framework to provide real-time visualization.
"""

import json
from datetime import datetime
from pathlib import Path
from typing import Any

from .base_agent import ActionResult, BaseAgent, Observation, ReasoningResult


class LiveAgentVisualizer:
    """Live visualizer that hooks into agent execution"""

    def __init__(self, output_dir: str = "agent_visualizations"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)

        self.session_data = {
            "session_id": datetime.now().strftime("%Y%m%d_%H%M%S"),
            "start_time": datetime.now().isoformat(),
            "phases": [],
            "actions": [],
            "statistics": {},
        }

        self.current_agent = None
        self.current_phase = None

    def start_session(self, agent: BaseAgent, code: str, error):
        """Start a new visualization session"""
        self.current_agent = agent
        self.session_data["agent_type"] = agent.__class__.__name__
        self.session_data["code_length"] = len(code)
        self.session_data["error_type"] = (
            error.error.name if hasattr(error, "error") else str(error)
        )

        self.log_phase(
            "SESSION_START",
            {"agent": agent.__class__.__name__, "error_type": self.session_data["error_type"]},
        )

        self.print_session_header()

    def log_phase(self, phase_name: str, data: dict[str, Any]):
        """Log a phase with timestamp"""
        phase_entry = {"phase": phase_name, "timestamp": datetime.now().isoformat(), "data": data}

        self.session_data["phases"].append(phase_entry)
        self.current_phase = phase_name

        self.print_phase_update(phase_name, data)

    def log_observation(self, observation: Observation):
        """Log the observation phase"""
        obs_data = {
            "error_location": observation.error_location,
            "error_text": (
                observation.error_text[:100] + "..."
                if len(observation.error_text) > 100
                else observation.error_text
            ),
            "context_length": len(observation.surrounding_context),
        }

        self.log_phase("OBSERVE", obs_data)

    def log_reasoning(self, reasoning: ReasoningResult):
        """Log the reasoning phase"""
        reasoning_data = {
            "primary_action": reasoning.primary_action.value,
            "secondary_actions": [a.value for a in reasoning.secondary_actions],
            "explanation": (
                reasoning.reasoning_explanation[:200] + "..."
                if len(reasoning.reasoning_explanation) > 200
                else reasoning.reasoning_explanation
            ),
        }

        self.log_phase("REASON", reasoning_data)

    def log_action(self, action_result: ActionResult):
        """Log the action phase and result"""
        candidates_info = ""
        # ActionResult always has candidates field
        if action_result.candidates:
            candidates_count = len(action_result.candidates)
            candidates_info = f" ({candidates_count} candidates)"

        # Get parameter summary for display (ActionResult always has this method)
        param_summary = action_result.get_parameter_summary()

        action_data = {
            "action": action_result.action_taken.value,
            "success": action_result.success,
            "explanation": action_result.explanation,
            "code_changed": action_result.modified_code
            != self.session_data.get("original_code", ""),
            "candidates_count": len(action_result.candidates),
            "has_multiple_candidates": len(action_result.candidates) > 1,
            "parameters": param_summary,
            "acceptance_criteria": (
                action_result.acceptance_evaluator.criteria.value
                if action_result.acceptance_evaluator
                else "default"
            ),
        }

        self.log_phase("ACT", action_data)

        # Add to actions list for statistics
        action_entry = {
            "timestamp": datetime.now().isoformat(),
            "action": action_result.action_taken.value,
            "success": action_result.success,
            "accepted": action_result.accepted,
            "explanation": action_result.explanation + candidates_info,
            "candidates_count": action_data["candidates_count"],
            "has_multiple_candidates": action_data["has_multiple_candidates"],
            "parameters": param_summary,
            "acceptance_criteria": action_data["acceptance_criteria"],
        }

        # Add detailed parameters (ActionResult always has action_parameters field)
        if action_result.action_parameters:
            action_entry["detailed_parameters"] = action_result.action_parameters

        self.session_data["actions"].append(action_entry)
        self.update_statistics()

    def log_acceptance(self, accepted: bool, feedback: str):
        """Log acceptance decision"""
        acceptance_data = {"accepted": accepted, "feedback": feedback}

        self.log_phase("ACCEPTANCE", acceptance_data)

        # Update the last action with acceptance status
        if self.session_data["actions"]:
            self.session_data["actions"][-1]["accepted"] = accepted
            self.session_data["actions"][-1]["acceptance_feedback"] = feedback

        self.update_statistics()

    def update_statistics(self):
        """Update session statistics"""
        actions = self.session_data["actions"]

        if not actions:
            return

        total_actions = len(actions)
        successful_actions = sum(1 for a in actions if a["success"])
        accepted_actions = sum(1 for a in actions if a.get("accepted", False))

        self.session_data["statistics"] = {
            "total_actions": total_actions,
            "successful_actions": successful_actions,
            "accepted_actions": accepted_actions,
            "success_rate": successful_actions / total_actions,
            "acceptance_rate": accepted_actions / total_actions if total_actions > 0 else 0,
        }

    def print_session_header(self):
        """Print session header"""
        print("🤖" + "=" * 70)
        print(f"   LIVE AGENT VISUALIZATION - {self.session_data['session_id']}")
        print("=" * 73)
        print(f"Agent: {self.session_data['agent_type']}")
        print(f"Error: {self.session_data['error_type']}")
        print(f"Code Length: {self.session_data['code_length']} characters")
        print("-" * 73)

    def print_phase_update(self, phase_name: str, data: dict[str, Any]):
        """Print real-time phase updates"""
        timestamp = datetime.now().strftime("%H:%M:%S")

        if phase_name == "SESSION_START":
            print(f"[{timestamp}] 🚀 Session started")

        elif phase_name == "OBSERVE":
            print(f"[{timestamp}] 👁️  OBSERVE: Analyzing error at lines {data['error_location']}")
            print(f"           Error: {data['error_text']}")

        elif phase_name == "REASON":
            print(f"[{timestamp}] 🧠 REASON: Selected {data['primary_action']}")
            if data["secondary_actions"]:
                print(f"           Backup: {', '.join(data['secondary_actions'])}")

        elif phase_name == "ACT":
            status = "✅" if data["success"] else "❌"
            candidates_info = ""
            if data.get("has_multiple_candidates", False):
                candidates_info = f" [{data.get('candidates_count', 1)} candidates]"

            print(f"[{timestamp}] ⚡ ACT: {data['action']} {status}{candidates_info}")
            print(f"           {data['explanation']}")

        elif phase_name == "ACCEPTANCE":
            status = "✅ ACCEPTED" if data["accepted"] else "❌ REJECTED"
            print(f"[{timestamp}] 📊 RESULT: {status}")
            print(f"           {data['feedback']}")

        print()

    def print_live_statistics(self):
        """Print live statistics"""
        stats = self.session_data.get("statistics", {})

        if not stats:
            return

        print("📈 LIVE STATISTICS")
        print("-" * 30)
        print(f"Actions: {stats['total_actions']}")
        print(f"Success Rate: {stats['success_rate']:.1%}")
        print(f"Acceptance Rate: {stats['acceptance_rate']:.1%}")
        print()

    def save_session(self):
        """Save session data to file"""
        self.session_data["end_time"] = datetime.now().isoformat()

        filename = self.output_dir / f"session_{self.session_data['session_id']}.json"
        with open(filename, "w") as f:
            json.dump(self.session_data, f, indent=2)

        print(f"📁 Session saved to {filename}")

    def generate_html_report(self):
        """Generate an HTML visualization report"""
        html_content = self.create_html_visualization()

        filename = self.output_dir / f"report_{self.session_data['session_id']}.html"
        with open(filename, "w") as f:
            f.write(html_content)

        print(f"🌐 HTML report generated: {filename}")
        return filename

    def create_html_visualization(self) -> str:
        """Create HTML visualization"""
        stats = self.session_data.get("statistics", {})
        actions = self.session_data.get("actions", [])

        html = f"""
<!DOCTYPE html>
<html>
<head>
    <title>Agent Repair Session - {self.session_data['session_id']}</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        .header {{ background: #f0f0f0; padding: 20px; border-radius: 5px; }}
        .phase {{ margin: 10px 0; padding: 10px; border-left: 4px solid #007acc; }}
        .action {{ margin: 10px 0; padding: 15px; background: #f9f9f9; border-radius: 5px; }}
        .success {{ border-left-color: green; }}
        .failure {{ border-left-color: red; }}
        .accepted {{ background: #e8f5e8; }}
        .rejected {{ background: #ffe8e8; }}
        .stats {{ display: flex; justify-content: space-around; margin: 20px 0; }}
        .stat-box {{ text-align: center; padding: 15px; background: #f0f8ff; border-radius: 5px; }}
    </style>
</head>
<body>
    <div class="header">
        <h1>🤖 Agent Repair Session Visualization</h1>
        <p><strong>Session ID:</strong> {self.session_data['session_id']}</p>
        <p><strong>Agent Type:</strong> {self.session_data['agent_type']}</p>
        <p><strong>Error Type:</strong> {self.session_data['error_type']}</p>
        <p><strong>Duration:</strong> {self.session_data.get('start_time', 'N/A')} - {self.session_data.get('end_time', 'Ongoing')}</p>
    </div>

    <h2>📊 Statistics</h2>
    <div class="stats">
        <div class="stat-box">
            <h3>{stats.get('total_actions', 0)}</h3>
            <p>Total Actions</p>
        </div>
        <div class="stat-box">
            <h3>{stats.get('success_rate', 0):.1%}</h3>
            <p>Success Rate</p>
        </div>
        <div class="stat-box">
            <h3>{stats.get('acceptance_rate', 0):.1%}</h3>
            <p>Acceptance Rate</p>
        </div>
    </div>

    <h2>🔄 Action Timeline</h2>
"""

        for i, action in enumerate(actions, 1):
            success_class = "success" if action["success"] else "failure"
            acceptance_class = "accepted" if action.get("accepted", False) else "rejected"

            html += f"""
    <div class="action {success_class} {acceptance_class}">
        <h4>Action {i}: {action['action']}</h4>
        <p><strong>Time:</strong> {action['timestamp']}</p>
        <p><strong>Branch:</strong> {action.get('branch', 'unknown')}</p>
        <p><strong>Success:</strong> {'✅' if action['success'] else '❌'}</p>
        <p><strong>Accepted:</strong> {'✅' if action.get('accepted', False) else '❌'}</p>
        <p><strong>Parameters:</strong> {action.get('parameters', 'No parameters')}</p>
        <p><strong>Explanation:</strong> {action['explanation']}</p>
        {f"<p><strong>Feedback:</strong> {action.get('acceptance_feedback', 'N/A')}</p>" if 'acceptance_feedback' in action else ""}
"""

            # Add detailed parameters if available
            if "detailed_parameters" in action and action["detailed_parameters"]:
                html += "<p><strong>Detailed Parameters:</strong></p><ul>"
                for param_name, param_value in action["detailed_parameters"].items():
                    if param_name != "guidance":  # Skip guidance in HTML for brevity
                        if isinstance(param_value, list):
                            html += f"<li>{param_name}: [{', '.join(map(str, param_value))}]</li>"
                        else:
                            html += f"<li>{param_name}: {param_value}</li>"
                html += "</ul>"

            html += "</div>"

        html += """
</body>
</html>
"""
        return html


# Decorator to automatically visualize agent methods
def visualized_agent(visualizer: LiveAgentVisualizer):
    """Decorator to add visualization to an agent"""

    def decorator(agent_class):
        original_repair = agent_class.repair
        original_observe = agent_class.observe
        original_reason = agent_class.reason
        original_act = agent_class.act

        def visualized_repair(self, code: str, error):
            visualizer.start_session(self, code, error)

            try:
                result = original_repair(self, code, error)
                visualizer.save_session()
                visualizer.generate_html_report()
                return result
            except Exception as e:
                visualizer.log_phase("ERROR", {"error": str(e)})
                visualizer.save_session()
                raise

        def visualized_observe(self, code: str, error):
            result = original_observe(self, code, error)
            visualizer.log_observation(result)
            return result

        def visualized_reason(self, observation):
            result = original_reason(self, observation)
            visualizer.log_reasoning(result)
            return result

        def visualized_act(self, observation, reasoning):
            result = original_act(self, observation, reasoning)
            visualizer.log_action(result)
            return result

        agent_class.repair = visualized_repair
        agent_class.observe = visualized_observe
        agent_class.reason = visualized_reason
        agent_class.act = visualized_act

        return agent_class

    return decorator
