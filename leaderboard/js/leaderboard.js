/**
 * Verus Proof Synthesis Leaderboard
 * Interactive JavaScript functionality
 */

// State management
const state = {
    currentBenchmark: 'verusage-bench',
    verusBenchData: null,
    verusageBenchData: null,
    sortColumn: 'percent_solved',
    sortDirection: 'desc'
};

// DOM Elements
const elements = {};

// Initialize the application
document.addEventListener('DOMContentLoaded', async () => {
    cacheElements();
    await loadData();
    setupEventListeners();
    render();
});

// Cache DOM elements for better performance
function cacheElements() {
    elements.tabButtons = document.querySelectorAll('.tab-button');
    elements.leaderboardBody = document.getElementById('leaderboard-body');
    elements.breakdownGrid = document.getElementById('breakdown-grid');
    elements.benchmarkTitle = document.getElementById('benchmark-title');
    elements.benchmarkDesc = document.getElementById('benchmark-desc');
    elements.statTasks = document.getElementById('stat-tasks');
    elements.statSubmissions = document.getElementById('stat-submissions');
    elements.statBestScore = document.getElementById('stat-best-score');
    elements.statLastUpdate = document.getElementById('stat-last-update');
    elements.tableHeaders = document.querySelectorAll('.leaderboard-table th.sortable');
}

// Load data from JSON files
async function loadData() {
    try {
        const [verusBench, verusageBench] = await Promise.all([
            fetch('data/verus-bench-results.json').then(r => r.json()),
            fetch('data/verusage-bench-results.json').then(r => r.json())
        ]);

        state.verusBenchData = verusBench;
        state.verusageBenchData = verusageBench;
    } catch (error) {
        console.error('Error loading data:', error);
        showError('Failed to load leaderboard data');
    }
}

// Setup event listeners
function setupEventListeners() {
    // Tab switching
    elements.tabButtons.forEach(button => {
        button.addEventListener('click', () => {
            const benchmark = button.dataset.benchmark;
            switchBenchmark(benchmark);
        });
    });

    // Table sorting
    elements.tableHeaders.forEach(header => {
        header.addEventListener('click', () => {
            const column = header.dataset.column;
            sortTable(column);
        });
    });
}

// Switch between benchmarks
function switchBenchmark(benchmark) {
    state.currentBenchmark = benchmark;
    state.sortColumn = 'percent_solved';
    state.sortDirection = 'desc';

    // Update tab styles
    elements.tabButtons.forEach(btn => {
        btn.classList.toggle('active', btn.dataset.benchmark === benchmark);
    });

    render();
}

// Sort table by column
function sortTable(column) {
    if (state.sortColumn === column) {
        state.sortDirection = state.sortDirection === 'desc' ? 'asc' : 'desc';
    } else {
        state.sortColumn = column;
        state.sortDirection = 'desc';
    }

    updateSortIndicators();
    renderLeaderboard();
}

// Update sort indicators in table headers
function updateSortIndicators() {
    elements.tableHeaders.forEach(header => {
        header.classList.remove('sorted-asc', 'sorted-desc');
        if (header.dataset.column === state.sortColumn) {
            header.classList.add(state.sortDirection === 'asc' ? 'sorted-asc' : 'sorted-desc');
        }
    });
}

// Main render function
function render() {
    const data = getCurrentData();
    if (!data) return;

    updateStats(data);
    updateBenchmarkInfo(data);
    renderLeaderboard();
    renderBreakdown(data);
}

// Get current benchmark data
function getCurrentData() {
    return state.currentBenchmark === 'verus-bench'
        ? state.verusBenchData
        : state.verusageBenchData;
}

// Update stats cards
function updateStats(data) {
    const bestScore = Math.max(...data.submissions.map(s => s.results.percent_solved));

    elements.statTasks.textContent = data.total_tasks;
    elements.statSubmissions.textContent = data.submissions.length;
    elements.statBestScore.textContent = bestScore.toFixed(1) + '%';
    elements.statLastUpdate.textContent = formatDate(data.last_updated);
}

// Update benchmark info
function updateBenchmarkInfo(data) {
    elements.benchmarkTitle.textContent = data.benchmark;
    elements.benchmarkDesc.textContent = data.description;
}

// Render leaderboard table
function renderLeaderboard() {
    const data = getCurrentData();
    if (!data) return;

    // Sort submissions
    const sorted = [...data.submissions].sort((a, b) => {
        let aVal, bVal;

        switch (state.sortColumn) {
            case 'percent_solved':
                aVal = a.results.percent_solved;
                bVal = b.results.percent_solved;
                break;
            case 'avg_time':
                aVal = a.results.avg_time_seconds || 0;
                bVal = b.results.avg_time_seconds || 0;
                break;
            case 'avg_cost':
                aVal = a.results.avg_cost_usd || a.results.total_cost_usd || 0;
                bVal = b.results.avg_cost_usd || b.results.total_cost_usd || 0;
                break;
            case 'system':
                aVal = a.system_name.toLowerCase();
                bVal = b.system_name.toLowerCase();
                return state.sortDirection === 'asc'
                    ? aVal.localeCompare(bVal)
                    : bVal.localeCompare(aVal);
            default:
                aVal = a.results.percent_solved;
                bVal = b.results.percent_solved;
        }

        return state.sortDirection === 'desc' ? bVal - aVal : aVal - bVal;
    });

    // Render rows
    elements.leaderboardBody.innerHTML = sorted.map((submission, index) => {
        const rank = index + 1;
        const score = submission.results.percent_solved;
        const scoreClass = score >= 80 ? 'high' : score >= 60 ? 'mid' : 'low';

        return `
      <tr class="fade-in" style="animation-delay: ${index * 0.05}s">
        <td>
          ${getRankDisplay(rank)}
        </td>
        <td>
          <div class="system-info">
            <span class="system-name">${escapeHtml(submission.system_name)}</span>
            <span class="model-name">${escapeHtml(submission.model)}</span>
          </div>
        </td>
        <td>
          <div class="score-bar">
            <span class="score score-${scoreClass}">${score.toFixed(1)}%</span>
            <div class="score-bar-track">
              <div class="score-bar-fill ${scoreClass}" style="width: ${score}%"></div>
            </div>
          </div>
        </td>
        <td>
          <span class="solved-count">${submission.results.solved} / ${submission.results.total}</span>
        </td>
        <td>
          ${submission.results.avg_time_seconds
                ? `<span class="time">${submission.results.avg_time_seconds.toFixed(1)}s</span>`
                : submission.results.avg_time_minutes
                    ? `<span class="time">${submission.results.avg_time_minutes.toFixed(1)}m</span>`
                    : '<span class="text-muted">-</span>'}
        </td>
        <td>
          ${submission.results.avg_cost_usd
                ? `<span class="cost">$${submission.results.avg_cost_usd.toFixed(2)}</span>`
                : submission.results.total_cost_usd
                    ? `<span class="cost">$${(submission.results.total_cost_usd / submission.results.total).toFixed(2)}</span>`
                    : '<span class="text-muted">-</span>'}
        </td>
        <td>
          ${submission.verified
                ? '<span class="verified-badge">Verified</span>'
                : ''}
        </td>
        <td>
          ${submission.paper_url
                ? `<a href="${escapeHtml(submission.paper_url)}" target="_blank" rel="noopener" class="link-icon tooltip" data-tooltip="Paper">📄</a>`
                : ''}
          ${submission.code_url
                ? `<a href="${escapeHtml(submission.code_url)}" target="_blank" rel="noopener" class="link-icon tooltip" data-tooltip="Code">💻</a>`
                : ''}
        </td>
      </tr>
    `;
    }).join('');

    updateSortIndicators();
}

// Get rank display with medal for top 3
function getRankDisplay(rank) {
    if (rank === 1) {
        return `<span class="rank rank-1"><span class="rank-medal">🥇</span> 1</span>`;
    } else if (rank === 2) {
        return `<span class="rank rank-2"><span class="rank-medal">🥈</span> 2</span>`;
    } else if (rank === 3) {
        return `<span class="rank rank-3"><span class="rank-medal">🥉</span> 3</span>`;
    }
    return `<span class="rank">${rank}</span>`;
}

// Render breakdown section
function renderBreakdown(data) {
    const categories = state.currentBenchmark === 'verus-bench'
        ? data.sources
        : data.projects;

    // Get the best submission for breakdown
    const bestSubmission = data.submissions.reduce((best, curr) =>
        curr.results.percent_solved > best.results.percent_solved ? curr : best
    );

    if (!bestSubmission.breakdown) {
        elements.breakdownGrid.innerHTML = '<p class="text-muted">No breakdown data available</p>';
        return;
    }

    // Create a map of breakdown data
    const breakdownMap = {};
    bestSubmission.breakdown.forEach(b => {
        breakdownMap[b.category] = b;
    });

    elements.breakdownGrid.innerHTML = categories.map((cat, index) => {
        const catCode = cat.code || cat.name;
        const catName = cat.name || cat.code;
        const breakdown = breakdownMap[catCode] || { solved: 0, total: cat.tasks };
        const percent = (breakdown.solved / breakdown.total * 100) || 0;

        return `
      <div class="breakdown-card fade-in" style="animation-delay: ${index * 0.05}s">
        <div class="breakdown-header">
          <span class="breakdown-title">${escapeHtml(catName)}</span>
          <span class="breakdown-tasks">${breakdown.total} tasks</span>
        </div>
        ${cat.domain ? `<div class="breakdown-domain" style="font-size: 0.75rem; color: var(--text-tertiary); margin-bottom: 0.5rem;">${escapeHtml(cat.domain)}</div>` : ''}
        <div class="breakdown-bar">
          <div class="breakdown-fill" style="width: ${percent}%"></div>
        </div>
        <div class="breakdown-stats">
          <span class="breakdown-percent">${percent.toFixed(1)}%</span>
          <span class="breakdown-count">${breakdown.solved} / ${breakdown.total}</span>
        </div>
      </div>
    `;
    }).join('');
}

// Utility functions
function formatDate(dateStr) {
    const date = new Date(dateStr);
    return date.toLocaleDateString('en-US', {
        year: 'numeric',
        month: 'short',
        day: 'numeric'
    });
}

function escapeHtml(str) {
    const div = document.createElement('div');
    div.textContent = str;
    return div.innerHTML;
}

function showError(message) {
    elements.leaderboardBody.innerHTML = `
    <tr>
      <td colspan="8" style="text-align: center; padding: 2rem; color: var(--accent-danger);">
        ${escapeHtml(message)}
      </td>
    </tr>
  `;
}
