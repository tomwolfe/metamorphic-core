import subprocess

class SelfHealingSystem:
    def __init__(self):
        self.health_status = "optimal"
        
    def heal_system(self):
        subprocess.run(["git", "checkout", "HEAD^"])
        return "System restored to last stable state"
