# src/api/server.py
from flask import Flask, jsonify, request
import os
import sys
import argparse
import logging
import redis
from src.core.llm_orchestration import LLMOrchestrator
from src.core.automation.workflow_driver import WorkflowDriver # Import WorkflowDriver
from src.api.routes.ethical_endpoints import ethical_bp
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address


startup_done = False

app = Flask(__name__)
limiter = Limiter(get_remote_address, app=app)

logging.basicConfig(level=logging.INFO)

llm_orchestrator = LLMOrchestrator()
app.llm_orchestrator = llm_orchestrator
workflow_driver = WorkflowDriver(llm_orchestrator) # Initialize WorkflowDriver
app.workflow_driver = workflow_driver # Expose to the app context

@app.route('/generate', methods=['POST']) # Direct route for /generate - Option 1
@limiter.limit("5/minute")
def generate_endpoint():
    prompt = request.get_json().get('prompt')
    return jsonify({"generated": "output-text"}), 200

@app.route('/genesis/test-endpoint')
def test_endpoint():
    return jsonify({"status": "test-route-working"}), 200

app.register_blueprint(ethical_bp, url_prefix='/genesis')

@app.before_request
def startup_debug():
    global startup_done
    if not startup_done:
        import socket
        hostname = socket.gethostname()
        ip = socket.gethostbyname(hostname)
        app.logger.info(f"Flask running on {ip}:5000")
        app.logger.info(f"Flask host binding to: 0.0.0.0:5000")
        try:
            redis_client = redis.Redis(host='localhost', port=6379)
            response = redis_client.ping()
            if response:
                app.logger.info("Redis connection successful")
            else:
                app.logger.warning("Redis ping failed but connection might still be alive.")
            app.logger.info("Placeholder: Successfully checked Redis connection (if configured)")
        except Exception as e:
            app.logger.error(f"Placeholder: Redis connection check failed (if configured): {str(e)}")
        app.logger.info("--- Environment Variables ---")
        keys_to_log = ['LLM_PROVIDER', 'GEMINI_API_KEY', 'YOUR_GITHUB_API_KEY', 'HUGGING_FACE_API_KEY', 'ZAP_API_KEY']
        for key in keys_to_log:
            value = os.environ.get(key, 'NOT SET')
            app.logger.info(f"{key}: {value}")
        app.logger.info("--- End Environment Variables ---")
        startup_done = True


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Metamorphic Core API')
    parser.add_argument('--task', type=str, help='Task description for WorkflowDriver')
    args = parser.parse_args()

    if args.task:
        with app.app_context():  # Access the WorkflowDriver from the Flask app context
            result = app.workflow_driver.execute_workflow(args.task)
            print(f"Workflow Result: {result}")
    else:
        app.run(debug=True, host='0.0.0.0')