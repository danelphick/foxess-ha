const WORK_MODES = {
  ForceCharge:    { label: 'Force Charge',    color: '#2196F3' },
  ForceDischarge: { label: 'Force Discharge', color: '#FF5722' },
  Feedin:         { label: 'Feed In',         color: '#4CAF50' },
  SelfUse:        { label: 'Self Use',        color: '#9C27B0' },
  Backup:         { label: 'Backup',          color: '#FF9800' },
};

class FoxESSSchedulerCard extends HTMLElement {
  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
  }

  set hass(hass) {
    this._hass = hass;
    this._render();
  }

  setConfig(config) {
    this._config = config || {};
  }

  getCardSize() { return 5; }

  _findEntities() {
    const states = this._hass.states;
    let schedulerEnabled = null;
    const slots = [];

    for (const [id, state] of Object.entries(states)) {
      if (!id.startsWith('sensor.')) continue;
      const attrs = state.attributes;
      if (attrs.start !== undefined && attrs.end !== undefined && attrs.min_soc_on_grid !== undefined) {
        slots.push(id);
      } else if (
        (state.state === 'enabled' || state.state === 'disabled') &&
        attrs.friendly_name?.toLowerCase().includes('scheduler')
      ) {
        schedulerEnabled = id;
      }
    }

    slots.sort((a, b) => {
      const n = id => parseInt(id.match(/_slot_(\d+)/)?.[1] ?? '99');
      return n(a) - n(b);
    });

    return { schedulerEnabled, slots };
  }

  _toMins(timeStr) {
    if (!timeStr) return -1;
    const [h, m] = timeStr.split(':').map(Number);
    return h * 60 + m;
  }

  _render() {
    if (!this._hass) return;

    const { schedulerEnabled, slots } = this._findEntities();
    if (!schedulerEnabled && slots.length === 0) {
      this.shadowRoot.innerHTML = `<ha-card><div style="padding:16px;color:var(--secondary-text-color)">No FoxESS scheduler entities found.</div></ha-card>`;
      return;
    }

    const now = new Date();
    const curMins = now.getHours() * 60 + now.getMinutes();
    const enabledState = schedulerEnabled ? (this._hass.states[schedulerEnabled]?.state ?? 'unavailable') : 'unavailable';

    const slotData = slots.map((id, idx) => {
      const s = this._hass.states[id];
      if (!s || s.state === 'unknown' || s.state === 'unavailable') return null;
      const { start, end, enabled, min_soc_on_grid, fd_soc, fd_pwr_w } = s.attributes;
      const startMins = this._toMins(start);
      const endMins = this._toMins(end);
      const isActive = enabled && s.state !== 'disabled' &&
        startMins >= 0 && endMins > startMins &&
        curMins >= startMins && curMins < endMins;
      return {
        idx: idx + 1, state: s.state, start, end, enabled,
        min_soc_on_grid, fd_soc, fd_pwr_w,
        startMins, endMins, isActive,
        cfg: WORK_MODES[s.state] ?? null,
      };
    }).filter(Boolean).filter(s => s.startMins !== s.endMins);

    const isRemaining = s => s.startMins === 0 && s.endMins === 1439;
    const remainingSlot = slotData.find(isRemaining) ?? null;
    const normalSlots = slotData.filter(s => !isRemaining(s));

    const toSeg = s => {
      const l = (s.startMins / 1440 * 100).toFixed(2);
      const w = ((s.endMins - s.startMins) / 1440 * 100).toFixed(2);
      return `<div class="seg${s.isActive ? ' seg-active' : ''}" data-slot="${s.idx}" style="left:${l}%;width:${w}%;background:${s.cfg.color}" title="${s.cfg.label}: ${s.start}–${s.end}"></div>`;
    };
    // Draw remaining slot first so other slots render on top of it.
    const remainingSeg = (remainingSlot?.enabled && remainingSlot?.cfg) ? toSeg(remainingSlot) : '';
    const normalSegs = normalSlots
      .filter(s => s.enabled && s.cfg && s.startMins >= 0 && s.endMins > s.startMins)
      .map(toSeg).join('');
    const segments = remainingSeg + normalSegs;

    const nowPct = (curMins / 1440 * 100).toFixed(2);

    const makeRow = (s, label, showTime) => {
      const color = (!s.enabled) ? '#9e9e9e' : (s.cfg?.color ?? '#9e9e9e');
      const badge = `<span class="badge" style="background:${color}22;color:${color};border-color:${color}55">${label}</span>`;
      const pwr = s.fd_pwr_w != null ? (s.fd_pwr_w / 1000).toFixed(1) + ' kW' : '—';
      return `<tr data-slot="${s.idx}" class="${s.isActive ? 'row-active' : ''} ${!s.enabled ? 'row-off' : ''}">
        <td>${showTime ? (s.start ?? '—') : ''}</td>
        <td>${showTime ? (s.end ?? '—') : ''}</td>
        <td>${badge}</td>
        <td>${s.min_soc_on_grid ?? '—'}%</td>
        <td>${s.fd_soc ?? '—'}%</td>
        <td>${pwr}</td>
      </tr>`;
    };
    const normalRows = normalSlots.map(s => makeRow(s, s.cfg ? s.cfg.label : s.state, true)).join('');
    const remainingRow = remainingSlot
      ? `<tr><td colspan="6" class="remaining-sep"></td></tr>${makeRow(remainingSlot, 'Remaining Time Slots', false)}`
      : '';
    const rows = normalRows + remainingRow;

    const statusCls = enabledState === 'enabled' ? 'status-on' : 'status-off';

    this.shadowRoot.innerHTML = `
      <style>
        ha-card { padding: 16px 16px 12px; }
        .hdr { display:flex; align-items:center; justify-content:space-between; margin-bottom:14px; }
        .title { font-size:1.1em; font-weight:500; color:var(--primary-text-color); }
        .status { font-size:.75em; font-weight:600; padding:2px 10px; border-radius:12px; text-transform:capitalize; border:1px solid; }
        .status-on  { background:#4caf5022; color:#4caf50; border-color:#4caf5066; }
        .status-off { background:#9e9e9e22; color:#9e9e9e; border-color:#9e9e9e66; }
        .tl { position:relative; height:24px; background:var(--divider-color,#e0e0e0); border-radius:5px; overflow:visible; margin-bottom:3px; }
        .seg { position:absolute; height:100%; border-radius:4px; opacity:.75; cursor:pointer; }
        .seg-active { opacity:1; box-shadow:0 1px 5px rgba(0,0,0,.3); }
        .seg.hovered { opacity:1; box-shadow:0 1px 8px rgba(0,0,0,.45); outline:2px solid rgba(255,255,255,.6); }
        .now { position:absolute; width:2px; height:32px; top:-4px; z-index:5; background:var(--primary-text-color,#333); border-radius:1px; pointer-events:none; }
        .tl-labels { display:flex; justify-content:space-between; font-size:.65em; color:var(--secondary-text-color); margin-bottom:12px; padding:0 1px; }
        table { width:100%; border-collapse:collapse; font-size:.82em; }
        th { padding:4px 5px; text-align:left; color:var(--secondary-text-color); font-weight:500; border-bottom:1px solid var(--divider-color); white-space:nowrap; }
        td { padding:5px 5px; color:var(--primary-text-color); white-space:nowrap; }
        .row-active td { background:rgba(3,169,244,.07); }
        .row-off td { color:var(--disabled-text-color,#aaa); }
        tr[data-slot] { cursor:pointer; }
        tr.hovered td { background:rgba(3,169,244,.15) !important; }
        .badge { font-size:.85em; padding:1px 8px; border-radius:10px; border:1px solid; }
        .remaining-sep { padding:5px 0 1px; border-top:1px solid var(--divider-color); }
      </style>
      <ha-card>
        <div class="hdr">
          <span class="title">FoxESS Scheduler</span>
          <span class="status ${statusCls}">${enabledState}</span>
        </div>
        <div class="tl">
          ${segments}
          <div class="now" style="left:${nowPct}%"></div>
        </div>
        <div class="tl-labels">
          <span>00:00</span><span>06:00</span><span>12:00</span><span>18:00</span><span>24:00</span>
        </div>
        <table>
          <thead><tr><th>Start</th><th>End</th><th>Mode</th><th>Min SoC</th><th>FD SoC</th><th>FD Power</th></tr></thead>
          <tbody>${rows}</tbody>
        </table>
      </ha-card>`;

    const root = this.shadowRoot;
    root.querySelectorAll('[data-slot]').forEach(el => {
      el.addEventListener('mouseenter', () => {
        root.querySelectorAll(`[data-slot="${el.dataset.slot}"]`).forEach(e => e.classList.add('hovered'));
      });
      el.addEventListener('mouseleave', () => {
        root.querySelectorAll(`[data-slot="${el.dataset.slot}"]`).forEach(e => e.classList.remove('hovered'));
      });
    });
  }
}

customElements.define('foxess-scheduler-card', FoxESSSchedulerCard);
window.customCards = window.customCards || [];
window.customCards.push({
  type: 'foxess-scheduler-card',
  name: 'FoxESS Scheduler',
  description: 'Displays the FoxESS inverter charge/discharge schedule with a 24-hour timeline.',
  preview: false,
});
