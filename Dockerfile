FROM python:3.11-slim

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY *.py ./
COPY public/ public/
COPY src/server.py ./src/ 2>/dev/null || true

RUN mkdir -p data/profile data/statuses data/threats data/uploads

EXPOSE 5000
EXPOSE 6789

CMD gunicorn --bind 0.0.0.0:5000 --workers 2 --threads 4 --timeout 120 run:app
