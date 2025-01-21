from flask import Flask, request, jsonify
from flask_limiter import Limiter
from src.core import ArchitectureGraph, QuantumCodeOptimizer
import google.generativeai as genai

app = Flask(__name__)
limiter = Limiter(app=app)
llm = genai.GenerativeModel('gemini-pro')

@app.route('/generate', methods=['POST'])
@limiter.limit("5/minute")
def generate_endpoint():
    return jsonify({"status": "System operational"})

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
