from textual.app import App, ComposeResult
from textual.widgets import Static

class WelcomeApp(App):
    CSS_PATH = "app_layout.tcss"

    def compose(self) -> ComposeResult:
        yield Static("One", classes="box")
        yield Static("Two [b](column-span: 2 and row-span: 2)", classes="box", id="two")
        yield Static("Three", classes="box")


if __name__ == "__main__":
    app = WelcomeApp()
    app.run()