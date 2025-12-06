from textual.app import App, ComposeResult
from textual.containers import Container, Horizontal, Vertical, VerticalScroll
from textual.screen import Screen, ModalScreen
from textual.widgets import (
    Button, Header, Footer, Input, Label, ListView, ListItem, 
    TextArea, Static, Markdown, Rule, Checkbox, LoadingIndicator
)
from textual.worker import Worker, get_current_worker, WorkerState
from textual.reactive import reactive
from textual.binding import Binding
from textual import on, log
import asyncio
import nest_asyncio
nest_asyncio.apply()
import sys
import json
import logging
import os
from openai import OpenAI
from dotenv import load_dotenv
import time
import re
from pydantic import BaseModel
from pathlib import Path

# Existing imports
from isabelle_client import get_isabelle_client, start_isabelle_server
from isabelle_client.isabelle_connector import IsabelleConnector
from isabelle_client.isabelle_connector import IsabelleTheoryError
from isabelle_client import IsabelleClient
# Constants
THEORY_REGEX = r"theory (.*)\n"
load_dotenv(".env")
TIMESTAMP = time.time()



# Now you can access them using os.environ
API_KEY = os.environ.get("OPENROUTER_API_KEY")

# Ensure outputs directory exists
Path("outputs").mkdir(exist_ok=True)

# Pydantic model for structured LLM output
class TestOutput(BaseModel):
    tests: list[str]

def get_theory_name(input_str: str) -> str | None:
    """Extract theory name from Isabelle theory content."""
    match = re.search(THEORY_REGEX, input_str)
    if match:
        return match.group(1).strip()
    return None

# LLM Wrapper
class LLM:
    def __init__(self):
        self.client = OpenAI(
            base_url="https://openrouter.ai/api/v1",
            api_key=API_KEY,
        )
        
    def generate(self, prompt: str) -> str:
        """Generate unstructured text response."""
        response = self.client.chat.completions.create(
            model="google/gemini-3-pro-preview",
            messages=[{"role": "user", "content": prompt}],
            extra_body={"reasoning": {"enabled": True}}
        )
        return response.choices[0].message.content
    
    def generate_with_output(self, prompt: str, structure) -> BaseModel:
        """Generate structured response using Pydantic model."""
        response = self.client.chat.completions.parse(
            model="mistralai/mistral-large-2512",
            messages=[{"role": "user", "content": prompt}],
            response_format=structure,
            extra_body={"reasoning": {"enabled": True}}
        )
        return response.choices[0].message.parsed

# Isabelle Wrapper
class Isabelle:
    def __init__(self):
        self.isabelle = self.connect()

    def connect(self):
        """Connect to Isabelle server."""
        server_info, _ = start_isabelle_server(
            name="test", port=9999, log_file="server.log"
        )
        isabelle = get_isabelle_client(server_info)
        # isabelle = IsabelleClient("test", 9999, "aa8d719b-4010-4775-98c2-9daf23240406")
        # isabelle.logger = logging.getLogger()
        # isabelle.logger.setLevel(logging.INFO)
        # isabelle.logger.addHandler(logging.FileHandler("session.log"))
        return isabelle

    def prove(self, llm_output: str) -> tuple[bool, list]:
        """
        Prove a theory and return (success, messages).
        
        Args:
            llm_output: The Isabelle theory content
            
        Returns:
            Tuple of (success_bool, list_of_messages)
        """
        theory_name = get_theory_name(llm_output)
        
        if theory_name is None:
            theory_name = f"Scratch_{int(time.time())}"
            llm_output = f'''theory {theory_name}
    imports Main
begin

{llm_output}

end'''

        # Write theory file
        with open(f"{theory_name}.thy", "w") as theory_file:
            theory_file.write(llm_output)

        # Try to prove it
        try:
            response = self.isabelle.use_theories(
                theories=[theory_name], master_dir=".", watchdog_timeout=0
            )
            return self.debug(response)
        except Exception as e:
            return False, [f"Isabelle error: {str(e)}"]

    def debug(self, response) -> tuple[bool, list]:
        """Parse Isabelle response and return success status with messages."""
        if not response:
            return False, ["Empty response from Isabelle"]
            
        last_response = response[-1].response_body
        response_data = json.loads(last_response)
        nodes = response_data['nodes'][0]
        messages = nodes['messages']
        
        if response_data['ok']:
            return True, ["Proof succeeded!"]
        
        error_messages = []
        for msg in messages:
            error_messages.append(msg.get('message', 'Unknown error'))
            
        return False, error_messages


# ==================== MODAL SCREENS ====================

class EditTestCaseModal(ModalScreen[str | None]):
    """Modal for editing a single test case."""
    
    def __init__(self, test_case: str = "", title: str = "Edit Test Case") -> None:
        super().__init__()
        self.test_case = test_case
        self.title = title

    def compose(self) -> ComposeResult:
        yield Container(
            Label(self.title, classes="modal-title"),
            TextArea(self.test_case, id="test_case_input"),
            Horizontal(
                Button("Save", variant="primary", id="save"),
                Button("Cancel", variant="default", id="cancel"),
                classes="modal-buttons"
            ),
            classes="edit-modal"
        )

    def on_mount(self) -> None:
        """Focus the text area when the modal opens."""
        self.query_one("#test_case_input", TextArea).focus()

    @on(Button.Pressed, "#save")
    def save_test_case(self, event: Button.Pressed) -> None:
        """Save the edited test case."""
        content = self.query_one("#test_case_input", TextArea).text
        self.dismiss(content)

    @on(Button.Pressed, "#cancel")
    def cancel_edit(self, event: Button.Pressed) -> None:
        """Cancel editing."""
        self.dismiss(None)


class TestCaseModal(ModalScreen[list[str] | None]):
    """Modal for reviewing and editing test cases."""
    
    def __init__(self, test_cases: list[str]) -> None:
        super().__init__()
        self.test_cases = test_cases.copy()  # Work with a copy

    def compose(self) -> ComposeResult:
        yield Container(
            Label("Review and Edit Test Cases", classes="modal-title"),
            Static("You can edit, delete, or add test cases before generating proofs.", classes="modal-subtitle"),
            VerticalScroll(
                ListView(id="test_case_list"),
                classes="test-case-list"
            ),
            Horizontal(
                Button("➕ Add Test Case", id="add_test_case", variant="success"),
                Button("✓ Confirm", id="confirm", variant="primary"),
                Button("✗ Cancel", id="cancel", variant="error"),
                classes="modal-buttons"
            ),
            classes="test-case-modal"
        )
    
    def on_mount(self) -> None:
        """Populate the list when the modal opens."""
        self.populate_list()
    
    def populate_list(self) -> None:
        """Populate the list view with test cases."""
        list_view = self.query_one("#test_case_list", ListView)
        list_view.clear()
        
        for i, test_case in enumerate(self.test_cases):
            item = ListItem(
                Horizontal(
                    Label(f"{i+1}. {test_case}", classes="test-case-text"),
                    Button("✎", id=f"edit_{i}", classes="small-button"),
                    Button("🗑", id=f"delete_{i}", classes="small-button danger"),
                    classes="test-case-item"
                ) #,
                # id=f"item_{i}"
            )
            list_view.append(item)

    @on(Button.Pressed, "#add_test_case")
    def add_test_case(self, event: Button.Pressed) -> None:
        """Add a new test case."""
        def handle_result(result: str | None) -> None:
            if result is not None and result.strip():
                self.test_cases.append(result.strip())
                self.populate_list()
        
        self.app.push_screen(EditTestCaseModal("", "New Test Case"), handle_result)

    @on(Button.Pressed, "#confirm")
    def confirm_test_cases(self, event: Button.Pressed) -> None:
        """Confirm and return the edited test cases."""
        self.dismiss(self.test_cases)

    @on(Button.Pressed, "#cancel")
    def cancel_test_cases(self, event: Button.Pressed) -> None:
        """Cancel and return None."""
        self.dismiss(None)

    @on(Button.Pressed)
    def handle_item_button(self, event: Button.Pressed) -> None:
        """Handle edit/delete buttons for individual test cases."""
        button_id = event.button.id
        
        if button_id and button_id.startswith("edit_"):
            index = int(button_id.split("_")[1])
            self.edit_test_case(index)
        elif button_id and button_id.startswith("delete_"):
            index = int(button_id.split("_")[1])
            self.delete_test_case(index)
    
    def edit_test_case(self, index: int) -> None:
        """Edit a specific test case."""
        def handle_result(result: str | None) -> None:
            if result is not None:
                self.test_cases[index] = result
                self.populate_list()
        
        self.app.push_screen(
            EditTestCaseModal(self.test_cases[index], f"Edit Test Case #{index + 1}"),
            handle_result
        )
    
    def delete_test_case(self, index: int) -> None:
        """Delete a specific test case."""
        self.test_cases.pop(index)
        self.populate_list()


class ProgressScreen(Screen):
    """Screen showing generation/proof progress."""
    
    def __init__(self, message: str = "Processing...") -> None:
        super().__init__()
        self.message = message
    
    def compose(self) -> ComposeResult:
        yield Container(
            Label(self.message, id="progress_message"),
            LoadingIndicator(id="spinner"),
            classes="progress-container"
        )
    
    def update_message(self, message: str) -> None:
        """Update the progress message."""
        self.query_one("#progress_message", Label).update(message)


class MainScreen(Screen):
    """Main application screen."""
    
    BINDINGS = [
        Binding(key="ctrl+i", action="quit", description="Quit"),
        Binding(key="ctrl+s", action="save_session", description="Save Session"),
    ]
    
    # Reactive state
    c_code_content = reactive("")
    test_cases = reactive([])
    theory_content = reactive("")
    proof_success = reactive(False)
    proof_messages = reactive([])
    filename = reactive("")

    def compose(self) -> ComposeResult:
        yield Header()
        yield Container(
            # File selection
            Vertical(
                Label("Code File:", classes="section-title"),
                Horizontal(
                    Input(placeholder="Enter path to code file...", id="file_input"),
                    Button("Browse...", id="browse", variant="default"),
                    classes="file-input-row"
                ),
                Static(id="file_status", classes="status-text"),
                classes="section"
            ),
            
            # Optional test case input
            Vertical(
                Label("Optional: Initial Test Case Description", classes="section-title"),
                TextArea(id="test_case_input", classes="test-case-textarea"),
                classes="section"
            ),
            
            # Action buttons
            Horizontal(
                Button("🚀 Generate Test Cases", id="generate_tests", variant="primary"),
                Button("📋 Show Theory", id="show_theory", variant="default"),
                Button("✓ Run Proof", id="run_proof", variant="success"),
                classes="action-buttons"
            ),
            
            # Results area
            Vertical(
                Label("Results:", classes="section-title"),
                Static("No results yet.", id="results", classes="results-area"),
                classes="section"
            ),
            
            classes="main-container"
        )
        yield Footer()
    
    def on_mount(self) -> None:
        """Set up initial state."""
        self.title = "Isabelle Proof Generator"
        self.sub_title = "AI-Powered Formal Verification"
    
    @on(Input.Changed, "#file_input")
    def on_file_input_changed(self, event: Input.Changed) -> None:
        """Handle file path input changes."""
        path = event.value.strip()
        status_widget = self.query_one("#file_status", Static)
        
        if not path:
            status_widget.update("")
            status_widget.set_classes("")
            return
        
        if os.path.isfile(path):
            try:
                with open(path) as f:
                    self.c_code_content = f.read()
                self.filename = os.path.basename(path)
                status_widget.update(
                    f"✓ Loaded: {self.filename} ({len(self.c_code_content)} chars)"
                )
                status_widget.set_classes("status-text success")
            except Exception as e:
                status_widget.update(f"✗ Error reading file: {e}")
                status_widget.set_classes("status-text error")
                self.c_code_content = ""
        else:
            status_widget.update("✗ File not found")
            status_widget.set_classes("status-text error")
            self.c_code_content = ""
    
    @on(Button.Pressed, "#browse")
    def browse_file(self, event: Button.Pressed) -> None:
        """Browse button handler - shows notification that it's not implemented."""
        self.notify("File browser not implemented. Please type the path manually.", severity="warning")
    
    @on(Button.Pressed, "#generate_tests")
    def generate_test_cases(self, event: Button.Pressed) -> None:
        """Generate test cases using LLM."""
        if not self.c_code_content:
            self.notify("Please select a valid C file first!", severity="error")
            return
        
        test_cases = self._generate_test_cases_worker()
        self._on_test_cases_generated(test_cases)
    
    def _generate_test_cases_worker(self) -> list[str]:
        """Worker function to generate test cases."""
        llm = LLM()
        
        test_prompt_input = f"""
Please analyze the following code and based on it, come up with test cases for what you think the expected behavior of the code should be. The code might be wrong but the translation should be based on what you think tests for correctness should be. Refer to any docstrings or comments for guidance on what correctness is - be realistic and don't return excessive amounts of test cases. The output should be a list of strings. 

Example Code:

// This class represents a savings account
class BankAccount {{
    private int balance = 0;

    public void deposit(int amount) {{
        balance += amount;
    }}

    public void withdraw(int amount) {{
        balance -= amount;
    }}
    public int getBalance() {{
        return balance;
    }}
}}

Example Output:
["The bank balance should never be negative.", "Depositing and withdrawing the same amount preserve total sum correctness"]

Do not try and infer the code based on any past CVE or context. The output should contain the python list and NOTHING ELSE.
Limit to 2-3 test cases

Please analyse the following code content.

{self.c_code_content}
"""
        
        # Get optional user test case
        user_test = self.query_one("#test_case_input", TextArea).text.strip()
        if user_test:
            test_prompt_input += f"\n\nAdditional context: {user_test}"
        
        self.app.push_screen(ProgressScreen("Generating test cases with AI..."))
        test_cases = llm.generate_with_output(test_prompt_input, TestOutput)
        return test_cases.tests if test_cases else []
    
    def _on_test_cases_generated(self, test_cases: list[str]) -> None:
        """Callback after test cases are generated."""
        self.test_cases = test_cases
        self.app.pop_screen()  # Close progress screen
        
        # Show modal for editing test cases
        def handle_modal_result(result: list[str] | None) -> None:
            if result is None:
                self.notify("Test case generation cancelled.", severity="warning")
                return
            
            self.test_cases = result
            self.notify(f"Confirmed {len(self.test_cases)} test cases!")
            self.query_one("#show_theory", Button).disabled = False
            self.query_one("#run_proof", Button).disabled = False
            
            # Show test cases in results
            results_text = f"Generated Test Cases:\n" + "\n".join(
                f"  {i+1}. {tc}" for i, tc in enumerate(self.test_cases)
            )
            self.query_one("#results", Static).update(results_text)
        
        self.app.push_screen(TestCaseModal(self.test_cases), handle_modal_result)
    
    @on(Button.Pressed, "#show_theory")
    def show_theory(self, event: Button.Pressed) -> None:
        """Display the generated Isabelle theory."""
        if not self.theory_content:
            self.notify("No theory generated yet. Click 'Run Proof' first.", severity="warning")
            return
        
        # Show theory in the results area
        results_text = f"Isabelle Theory:\n{'='*50}\n{self.theory_content}"
        self.query_one("#results", Static).update(results_text)
    
    @on(Button.Pressed, "#run_proof")
    async def generate_and_prove(self, event: Button.Pressed) -> None:
        """Generate Isabelle theory and run proof."""
        if not self.c_code_content or not self.test_cases:
            self.notify("Missing code or test cases!", severity="error")
            return
        
        # Show progress
        progress_screen = ProgressScreen("Generating Isabelle theory...")
        self.app.push_screen(progress_screen)
        
        # Run in worker
        worker = self.run_worker(
            self._generate_and_prove_worker(),
            exclusive=True,
            thread=True
        )
        theory = worker.wait()
        print(theory)

        # theory = ""

        # worker.add_callback(self._on_proof_complete)
        # theory = self._generate_and_prove_worker()
        # self._on_proof_complete(theory)
    
    def on_worker_state_changed(self, event: Worker.StateChanged) -> None:
        # self.log(event)
        if event.state == WorkerState.SUCCESS:
            self._on_proof_complete(event.worker.result)

    async def _generate_and_prove_worker(self) -> tuple[str, bool, list[str]]:
        """Worker function to generate theory and run proof."""
        llm = LLM()
        isabelle = Isabelle()
        
        # Generate Isabelle theory
        isabelle_prompt = f"""
Please translate the following code into corresponding isabelle language formal problem. Just translate, do not provide any other text or comments. Always write a proof, even if the software has bugs: if the software is buggy, the intended behavior is that Isabelle will notify that there's an error and the program itself should not do so, so never say sorry or oops.

Example Code:
year = ORIGINYEAR;
while (days > 365) {{
    if (IsLeapYear (year)) {{
        if (days > 366) {{
            days -= days 366;
            year += 1;
        }}
    }} else {{
        days -= 365;
        year += 1;
    }}
}}

Example Output:
fun zune_step :: "nat ⇒ nat ⇒ (nat × nat)" where
    "zune_step days year =
        (if days > 365 then
            (if isLeapYear year then
                (if days > 366 then (days - 366, year + 1)
                else (days, year))
            else (days - 365, year + 1))
        else (days, year))"

fun zune_loop :: "nat ⇒ nat ⇒ nat ⇒ (nat × nat)" where
"zune_loop fuel days year =
    (if fuel = 0 then (days, year)
    else let (d', y') = zune_step days year
        in if d' = days ∧ y' = year then (d', y')
            else zune_loop (fuel - 1) d' y')"

lemma zune_bug_stuck:
    assumes "isLeapYear year" and "days = 366"
    shows "zune_step days year = (days, year)"
    using assms by simp

Note that you should only output the body of the Isabelle proof - you do not have to include filename, headers, imports, or codeblock markers. The generated code will go in here:
```isabelle
theory Example
imports Main
begin
<YOUR OUTPUT>
end
```

Write a proof in the Isabelle language. The first step is to convert the given code to fit Isabelle

```
{self.c_code_content}
```

Without using any context of the provided code, next write lemmas that formally prove that {self.test_cases}. 

Requirements for the lemma(s):
- Do NOT strengthen the statement to make it true.
- Do NOT add assumptions to make it provable.
- If the test case describes a false property, Isabelle must fail. This is correct behavior.
- Do NOT use "sorry" or "oops".
- DO NOT USE ANY COMMENTS.
"""

        self.theory_content = llm.generate(isabelle_prompt)

        # Run proof
        success, messages = isabelle.prove(self.theory_content)
        return self.theory_content, success, messages
    
    def _on_proof_complete(self, result: tuple[str, bool, list[str]]) -> None:
        """Callback after proof is complete."""
        self.app.pop_screen()  # Close progress screen

        theory_content, success, messages = result
        
        self.theory_content = theory_content
        self.proof_success = success
        self.proof_messages = messages
        
        # Save results
        timestamp = time.time()
        with open(f"outputs/output_{timestamp}.thy", "w") as f:
            f.write(theory_content)
        
        with open(f"outputs/proof_result_{timestamp}.txt", "w") as f:
            f.write(f"Success: {success}\n")
            f.write("\n".join(messages))
        
        # Update UI
        status = "✅ SUCCESS" if success else "❌ FAILED"
        results_text = f"""
Proof Result: {status}

Messages:
{'-'*50}
{chr(10).join(messages)}

Theory saved to: outputs/output_{timestamp}.thy
Result saved to: outputs/proof_result_{timestamp}.txt
"""
        self.query_one("#results", Static).update(results_text)
        
        if success:
            self.notify("Proof completed successfully!", severity="information")
        else:
            self.notify("Proof failed. Check messages for details.", severity="error")
    
    def action_quit(self) -> None:
        self.app.exit()

    def action_save_session(self) -> None:
        """Save current session to file."""
        if not self.c_code_content:
            self.notify("Nothing to save!", severity="warning")
            return
        
        timestamp = time.time()
        session_data = {
            "filename": self.filename,
            "c_code": self.c_code_content,
            "test_cases": self.test_cases,
            "theory": self.theory_content,
            "proof_success": self.proof_success,
            "proof_messages": self.proof_messages,
            "timestamp": timestamp
        }
        
        with open(f"outputs/session_{timestamp}.json", "w") as f:
            json.dump(session_data, f, indent=2)
        
        self.notify(f"Session saved to outputs/session_{timestamp}.json", severity="information")


# ==================== STYLES ====================

STYLES = """
/* Main layout */
.main-container {
    layout: vertical;
    height: 1fr;
    padding: 1 2;
    overflow-y: auto;
}

.section {
    height: auto;
    margin: 1 0;
}

.section-title {
    text-style: bold;
    color: $accent;
    margin-bottom: 1;
}

/* File input */
.file-input-row {
    height: auto;
    layout: horizontal;
}

#file_input {
    width: 1fr;
}

#browse {
    width: 12;
    margin-left: 1;
}

.status-text {
    margin-top: 1;
    height: auto;
}

.status-text.success {
    color: $success;
}

.status-text.error {
    color: $error;
}

/* Test case textarea */
.test-case-textarea {
    height: 6;
    border: solid $primary;
}

/* Action buttons */
.action-buttons {
    height: auto;
    layout: horizontal;
    margin: 2 0;
}

.action-buttons Button {
    margin-right: 1;
}

/* Results area */
.results-area {
    height: auto;
    min-height: 10;
    border: solid $primary;
    padding: 1;
    background: $surface;
}

/* Modal styles */
.edit-modal {
    width: 80;
    height: auto;
    max-height: 20;
    padding: 2;
    background: $surface;
    border: thick $primary;
}

.test-case-modal {
    width: 90;
    height: auto;
    max-height: 30;
    padding: 2;
    background: $surface;
    border: thick $primary;
}

.modal-title {
    text-style: bold;
    text-align: center;
    color: $accent;
    margin-bottom: 1;
}

.modal-subtitle {
    text-align: center;
    color: $text-muted;
    margin-bottom: 1;
}

.modal-buttons {
    height: auto;
    layout: horizontal;
    margin-top: 1;
}

.modal-buttons Button {
    margin-right: 1;
}

/* Test case list */
.test-case-list {
    height: auto;
    max-height: 15;
    border: solid $primary;
    margin: 1 0;
}

ListItem {
    padding: 1;
    border-bottom: solid $surface-lighten-1;
}

.test-case-item {
    height: auto;
    layout: horizontal;
    align: center middle;
}

.test-case-text {
    width: 1fr;
}

.small-button {
    width: 3;
    margin-left: 1;
}

.small-button.danger {
    background: $error;
}

/* Progress screen */
.progress-container {
    layout: vertical;
    align: center middle;
    height: 100%;
    background: $background;
}

#progress_message {
    text-style: bold;
    margin-bottom: 2;
}

#spinner {
    width: 10;
    height: 5;
}
"""


# ==================== MAIN APP ====================

class IsabelleProofApp(App):
    """Main TUI application for Isabelle proof generation."""
    
    CSS = STYLES
    SCREENS = {
        "main": MainScreen,
    }
    
    def on_mount(self) -> None:
        """Set up the application."""
        self.push_screen("main")


if __name__ == "__main__":
    # isabelle = Isabelle()
    app = IsabelleProofApp()
    app.run()